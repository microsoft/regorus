// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::value::{Array, Object, Set};
use regorus::{Engine, Rc, Value};
use std::collections::{BTreeMap, BTreeSet};

mod native_depth_support;

const WORKER_STACK_BYTES: usize = 1_048_576;
const DEPTH: usize = 16_384;

#[derive(Clone, Copy, Debug)]
enum Shape {
    Array,
    Set,
    FrozenValue,
    BTreeValue,
    FrozenKey,
    BTreeKey,
    Mixed,
}

const SHAPES: [Shape; 7] = [
    Shape::Array,
    Shape::Set,
    Shape::FrozenValue,
    Shape::BTreeValue,
    Shape::FrozenKey,
    Shape::BTreeKey,
    Shape::Mixed,
];

fn nested(depth: usize, mut value: Value, shape: Shape) -> Value {
    for level in 0..depth {
        let shape = if matches!(shape, Shape::Mixed) {
            SHAPES[level % 6]
        } else {
            shape
        };
        value = match shape {
            Shape::Array => Array::from(vec![value]).into_value(),
            Shape::Set => Set::from(BTreeSet::from([value])).into_value(),
            Shape::FrozenValue => Object::from(BTreeMap::from([(Value::Null, value)])).into_value(),
            Shape::BTreeValue => Value::Object(Rc::new(Object::from(BTreeMap::from([(
                Value::Null,
                value,
            )])))),
            Shape::FrozenKey => Object::from(BTreeMap::from([(value, Value::Null)])).into_value(),
            Shape::BTreeKey => Value::Object(Rc::new(Object::from(BTreeMap::from([(
                value,
                Value::Null,
            )])))),
            Shape::Mixed => unreachable!(),
        };
    }
    value
}

fn isolated(test_name: &str, body: fn()) {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess(test_name);
        return;
    }
    // RUST_MIN_STACK in the subprocess helper applies to the harness, not this worker.
    std::thread::Builder::new()
        .name(test_name.into())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

fn leaf() -> Rc<str> {
    Rc::from("destructor-only leaf")
}

fn released<T>(label: &str, value: T, sentinel: &Rc<str>) {
    released_with_owners(label, value, sentinel, 2);
}

fn released_with_owners<T>(label: &str, value: T, sentinel: &Rc<str>, owners: usize) {
    // Mark completed construction without formatting, comparing, or serializing the value.
    eprintln!("constructed: {label}");
    assert_eq!(Rc::strong_count(sentinel), owners);
    drop(value);
    assert_eq!(Rc::strong_count(sentinel), 1, "{label}: retained leaf");
    eprintln!("destroyed: {label}");
}

fn bare_and_rc<T>(owner: Rc<T>, mode: usize, sentinel: &Rc<str>) {
    match mode {
        0 => released(
            "bare wrapper from try_unwrap",
            Rc::try_unwrap(owner).ok().unwrap(),
            sentinel,
        ),
        1 => released("bare Rc payload", owner, sentinel),
        _ => released(
            "bare wrapper from into_inner",
            Rc::into_inner(owner).unwrap(),
            sentinel,
        ),
    }
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn destructor_only_1048576_byte_stack() {
    isolated("destructor_only_1048576_byte_stack", || {
        for shape in SHAPES {
            eprintln!("constructing: {shape:?}");
            let sentinel = leaf();
            released(
                "Value root",
                nested(DEPTH, Value::String(sentinel.clone()), shape),
                &sentinel,
            );
            for mode in 0..3 {
                let value = nested(DEPTH, Value::String(sentinel.clone()), shape);
                match value {
                    Value::Array(owner) => bare_and_rc(owner, mode, &sentinel),
                    Value::Set(owner) => bare_and_rc(owner, mode, &sentinel),
                    Value::Object(owner) => bare_and_rc(owner, mode, &sentinel),
                    _ => unreachable!(),
                }
            }
        }

        let sentinel = leaf();
        let mut engine = Engine::new();
        engine.set_input(nested(DEPTH, Value::String(sentinel.clone()), Shape::Mixed));
        eprintln!("constructed: Engine input before overwrite");
        engine.set_input(Value::Null);
        assert_eq!(Rc::strong_count(&sentinel), 1);
        eprintln!("destroyed: Engine input by overwrite");
        engine.set_input(nested(DEPTH, Value::String(sentinel.clone()), Shape::Mixed));
        released("Engine owning input", engine, &sentinel);

        #[cfg(feature = "rvm")]
        {
            let mut vm = regorus::rvm::vm::RegoVM::new();
            vm.set_input(nested(DEPTH, Value::String(sentinel.clone()), Shape::Mixed));
            eprintln!("constructed: RegoVM input before overwrite");
            vm.set_input(Value::Null);
            assert_eq!(Rc::strong_count(&sentinel), 1);
            eprintln!("destroyed: RegoVM input by overwrite");
            vm.set_input(nested(DEPTH, Value::String(sentinel.clone()), Shape::Mixed));
            released("RegoVM owning input", vm, &sentinel);
        }
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn branching_destructor_only_1048576_byte_stack() {
    isolated("branching_destructor_only_1048576_byte_stack", || {
        let sentinel = leaf();
        let children = || {
            [
                nested(DEPTH, Value::String(sentinel.clone()), Shape::Array),
                nested(DEPTH, Value::String(sentinel.clone()), Shape::Set),
            ]
        };
        released_with_owners(
            "array with two deep children",
            Array::from(Vec::from(children())),
            &sentinel,
            3,
        );
        released_with_owners(
            "set with two deep children",
            Set::from(BTreeSet::from(children())),
            &sentinel,
            3,
        );
        for frozen in [false, true] {
            let [key, value] = children();
            let object = Object::from(BTreeMap::from([(key, value)]));
            let value = if frozen {
                object.into_value()
            } else {
                Value::Object(Rc::new(object))
            };
            released_with_owners("object with deep key and value", value, &sentinel, 3);
        }

        // Retain a sibling at every level, exercising continuation growth as well
        // as the single-child fast path. No zero-allocation claim applies here.
        let depth = 4096;
        let mut value = Value::Null;
        for level in 0..depth {
            let sibling = Value::String(sentinel.clone());
            value = match level % 4 {
                0 => Array::from(vec![value, sibling]).into_value(),
                1 => Set::from(BTreeSet::from([value, sibling])).into_value(),
                2 => Object::from(BTreeMap::from([(value, sibling)])).into_value(),
                _ => Value::Object(Rc::new(Object::from(BTreeMap::from([(value, sibling)])))),
            };
        }
        released_with_owners("mixed branching ladder", value, &sentinel, depth + 1);
    });
}

fn cow_payload<T: Clone>(mut owner: Rc<T>, clear: fn(&mut T), sentinel: &Rc<str>) {
    let original = owner.clone();
    eprintln!("constructed: shared payload before COW clear");
    clear(Rc::make_mut(&mut owner));
    assert!(!Rc::ptr_eq(&owner, &original));
    assert_eq!(Rc::strong_count(sentinel), 2);
    drop(owner);
    assert_eq!(Rc::strong_count(sentinel), 2);
    drop(original);
    assert_eq!(Rc::strong_count(sentinel), 1);
}

fn weak_payload<T: Clone>(mut owner: Rc<T>, clear: fn(&mut T), sentinel: &Rc<str>) {
    let weak = Rc::downgrade(&owner);
    eprintln!("constructed: sole strong payload with Weak");
    clear(Rc::make_mut(&mut owner));
    assert!(weak.upgrade().is_none(), "make_mut must dissociate Weak");
    assert_eq!(Rc::strong_count(sentinel), 1);
    drop(owner);
    drop(weak);
}

fn weak_into_inner<T>(owner: Rc<T>, sentinel: &Rc<str>) {
    let weak = Rc::downgrade(&owner);
    let payload = Rc::into_inner(owner).expect("Weak does not prevent into_inner");
    assert!(weak.upgrade().is_none());
    released("unwrapped payload with surviving Weak", payload, sentinel);
    drop(weak);
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn shared_cow_and_weak_1048576_byte_stack() {
    isolated("shared_cow_and_weak_1048576_byte_stack", || {
        for shape in SHAPES {
            eprintln!("constructing sharing cases: {shape:?}");
            let sentinel = leaf();
            for mode in 0..3 {
                let value = nested(DEPTH, Value::String(sentinel.clone()), shape);
                match (value, mode) {
                    (Value::Array(owner), 0) => cow_payload(owner, Array::clear, &sentinel),
                    (Value::Set(owner), 0) => cow_payload(owner, Set::clear, &sentinel),
                    (Value::Object(owner), 0) => cow_payload(owner, Object::clear, &sentinel),
                    (Value::Array(owner), 1) => weak_payload(owner, Array::clear, &sentinel),
                    (Value::Set(owner), 1) => weak_payload(owner, Set::clear, &sentinel),
                    (Value::Object(owner), 1) => weak_payload(owner, Object::clear, &sentinel),
                    (Value::Array(owner), _) => weak_into_inner(owner, &sentinel),
                    (Value::Set(owner), _) => weak_into_inner(owner, &sentinel),
                    (Value::Object(owner), _) => weak_into_inner(owner, &sentinel),
                    _ => unreachable!(),
                }
            }

            let shared = nested(DEPTH, Value::String(sentinel.clone()), shape);
            let survivor = shared.clone();
            let root = Array::from(vec![shared.clone(), shared]).into_value();
            eprintln!("constructed: diamond DAG with external survivor");
            drop(root);
            assert_eq!(Rc::strong_count(&sentinel), 2);
            released("last DAG owner", survivor, &sentinel);

            let shared = nested(DEPTH, Value::String(sentinel.clone()), shape);
            released(
                "diamond DAG with no external owner",
                Array::from(vec![shared.clone(), shared]),
                &sentinel,
            );
        }
    });
}

#[test]
#[cfg(feature = "arc")]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn concurrent_arc_final_releases_1048576_byte_stack() {
    isolated("concurrent_arc_final_releases_1048576_byte_stack", || {
        use std::sync::{Arc, Barrier};
        for shape in SHAPES {
            for _ in 0..8 {
                let sentinel = leaf();
                let shared = nested(4096, Value::String(sentinel.clone()), shape);
                let barrier = Arc::new(Barrier::new(5));
                let mut workers = Vec::new();
                for _ in 0..4 {
                    let root = Array::from(vec![shared.clone()]);
                    let barrier = barrier.clone();
                    workers.push(
                        std::thread::Builder::new()
                            .stack_size(WORKER_STACK_BYTES)
                            .spawn(move || {
                                barrier.wait();
                                drop(root);
                                #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
                                regorus::flush_thread_memory_counters();
                            })
                            .unwrap(),
                    );
                }
                drop(shared);
                eprintln!("constructed: concurrent final Arc owners {shape:?}");
                barrier.wait();
                // Every final owner releases through release_values -> Rc::into_inner.
                for worker in workers {
                    worker.join().unwrap();
                }
                assert_eq!(Rc::strong_count(&sentinel), 1, "{shape:?}: leaked leaf");
            }
        }
    });
}

// Keep this allocator local to this integration binary. Mimalloc builds instead
// exercise their own accounting below, without replacing the production allocator.
#[cfg(all(not(feature = "mimalloc"), not(miri)))]
mod allocation_probe {
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::cell::Cell;

    #[derive(Clone, Copy, Default)]
    pub struct Stats {
        pub allocations: usize,
        pub freed_bytes: usize,
    }

    thread_local! {
        static ACTIVE: Cell<bool> = const { Cell::new(false) };
        static STATS: Cell<Stats> = const { Cell::new(Stats {
            allocations: 0,
            freed_bytes: 0,
        }) };
    }

    struct Probe;

    #[global_allocator]
    static ALLOCATOR: Probe = Probe;

    fn record(allocation: bool, freed_bytes: usize) {
        if ACTIVE.try_with(Cell::get).unwrap_or(false) {
            let _ = STATS.try_with(|stats| {
                let mut current = stats.get();
                current.allocations += usize::from(allocation);
                current.freed_bytes += freed_bytes;
                stats.set(current);
            });
        }
    }

    unsafe impl GlobalAlloc for Probe {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let pointer = System.alloc(layout);
            record(true, 0);
            pointer
        }

        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            let pointer = System.alloc_zeroed(layout);
            record(true, 0);
            pointer
        }

        unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
            let replacement = System.realloc(pointer, layout, size);
            record(true, 0);
            replacement
        }

        unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
            record(false, layout.size());
            System.dealloc(pointer, layout);
        }
    }

    struct Guard;

    impl Drop for Guard {
        fn drop(&mut self) {
            ACTIVE.with(|active| active.set(false));
        }
    }

    pub fn measure(operation: impl FnOnce()) -> Stats {
        STATS.with(|stats| stats.set(Stats::default()));
        ACTIVE.with(|active| assert!(!active.replace(true)));
        let guard = Guard;
        operation();
        drop(guard);
        STATS.with(Cell::get)
    }
}

#[test]
#[cfg(all(not(feature = "mimalloc"), not(miri)))]
fn single_child_array_set_chains_allocate_nothing_while_dropping() {
    isolated(
        "single_child_array_set_chains_allocate_nothing_while_dropping",
        || {
            for shape in [Shape::Array, Shape::Set] {
                let sentinel = leaf();
                let value = nested(DEPTH, Value::String(sentinel.clone()), shape);
                eprintln!("constructed: allocation probe {shape:?}");
                let stats = allocation_probe::measure(|| drop(value));
                assert_eq!(stats.allocations, 0, "{shape:?}");
                assert!(stats.freed_bytes > DEPTH);
                assert_eq!(Rc::strong_count(&sentinel), 1);
            }
            // Alternating single-child array/set frames need no continuation stack either.
            let sentinel = leaf();
            let mut value = Value::String(sentinel.clone());
            for level in 0..DEPTH {
                value = nested(
                    1,
                    value,
                    if level % 2 == 0 {
                        Shape::Array
                    } else {
                        Shape::Set
                    },
                );
            }
            eprintln!("constructed: alternating allocation probe");
            let stats = allocation_probe::measure(|| drop(value));
            assert_eq!(stats.allocations, 0);
            assert!(stats.freed_bytes > DEPTH);
            assert_eq!(Rc::strong_count(&sentinel), 1);
        },
    );
}

#[test]
#[cfg(all(not(feature = "mimalloc"), not(miri)))]
fn exhausted_object_iterators_do_not_accumulate_continuation_frames() {
    isolated(
        "exhausted_object_iterators_do_not_accumulate_continuation_frames",
        || {
            for shape in [Shape::FrozenValue, Shape::BTreeValue] {
                let sentinel = leaf();
                let value = nested(DEPTH, Value::String(sentinel.clone()), shape);
                eprintln!("constructed: exhausted Object iterator probe {shape:?}");
                let stats = allocation_probe::measure(|| drop(value));
                // A scalar key followed by its only value needs one reusable scratch
                // allocation, not one retained iterator frame per nesting level.
                assert_eq!(stats.allocations, 1, "{shape:?}");
                assert!(stats.freed_bytes > DEPTH);
                assert_eq!(Rc::strong_count(&sentinel), 1);
            }
        },
    );
}

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
struct MemoryLimitGuard(Option<u64>);

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
impl Drop for MemoryLimitGuard {
    fn drop(&mut self) {
        regorus::set_global_memory_limit(self.0);
    }
}

#[test]
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
fn cooperative_limit_does_not_prevent_destruction_or_leak_live_bytes() {
    isolated(
        "cooperative_limit_does_not_prevent_destruction_or_leak_live_bytes",
        || {
            use mimalloc::limits::{with_memory_budget_usage_scope, MemoryBudgetUsage};

            let _limit_guard = MemoryLimitGuard(regorus::global_memory_limit());
            for shape in SHAPES {
                regorus::set_global_memory_limit(None);
                let sentinel = leaf();
                eprintln!("constructing: cooperative-limit accounting {shape:?}");
                let baseline = mimalloc::current_thread_live_bytes();
                let value = nested(DEPTH, Value::String(sentinel.clone()), shape);
                let constructed = mimalloc::current_thread_live_bytes();
                assert!(constructed > baseline + DEPTH as i64);
                eprintln!("constructed: cooperative-limit accounting {shape:?}");
                regorus::set_global_memory_limit(Some(1));
                assert!(matches!(
                    regorus::enforce_memory_limit(),
                    Err(regorus::LimitError::MemoryLimitExceeded { limit: 1, .. })
                ));

                let mut charged = None;
                // This is a cooperative limit, not physical OOM or a failing allocator.
                // Destruction may allocate scratch space for objects/branching shapes.
                with_memory_budget_usage_scope(
                    Some(MemoryBudgetUsage::default()),
                    &mut charged,
                    || drop(value),
                );
                let after = mimalloc::current_thread_live_bytes();
                let charged = charged.unwrap().requested_bytes();
                assert_eq!(after, baseline, "{shape:?}: live bytes did not recover");
                assert_eq!(Rc::strong_count(&sentinel), 1);
                if matches!(shape, Shape::Array | Shape::Set) {
                    assert_eq!(charged, 0, "{shape:?}: single-child chain allocated");
                } else {
                    assert!(charged > 0, "{shape:?}: scratch allocation was not charged");
                }
                assert_eq!(regorus::global_memory_limit(), Some(1));
                regorus::set_global_memory_limit(None);
            }
            regorus::flush_thread_memory_counters();
        },
    );
}
