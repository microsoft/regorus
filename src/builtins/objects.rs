// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_object};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::iter::Iterator;
use std::rc::Rc;

use anyhow::{bail, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("json.filter", (json_filter, 2));
    //    m.insert("json.patch", (json_patch));
    m.insert("object.filter", (filter, 2));
    m.insert("object.get", (get, 3));
    m.insert("object.keys", (keys, 1));
    m.insert("object.remove", (remove, 2));
    m.insert("object.subset", (subset, 2));
}

fn json_filter_impl(v: &Value, filter: &Value) -> Value {
    let filters = match filter {
        Value::Object(fields) if !fields.is_empty() => fields,
        _ => return v.clone(),
    };

    match v {
        Value::Array(_) => {
            let mut items = vec![];
            for (idx, filter) in filters.iter() {
                // The string index must be parseable as a number.
                // TODO: support integer indexes?
                if let Value::String(idx) = idx {
                    if let Ok(idx) = Value::from_json_str(idx) {
                        let item = json_filter_impl(&v[&idx], filter);
                        if item != Value::Undefined {
                            items.push(item);
                        }
                    }
                }
            }
            Value::from_array(items)
        }

        Value::Set(s) => {
            let mut items = BTreeSet::new();
            for (item, filter) in filters.iter() {
                if s.contains(item) {
                    let item = json_filter_impl(item, filter);
                    if item != Value::Undefined {
                        items.insert(item);
                    }
                }
            }
            Value::from_set(items)
        }

        Value::Object(_) => {
            let mut items = BTreeMap::new();
            for (key, filter) in filters.iter() {
                let item = json_filter_impl(&v[key], filter);
                if item != Value::Undefined {
                    items.insert(key.clone(), item);
                }
            }

            Value::from_map(items)
        }

        _ => Value::Undefined,
    }
}

fn merge_filters(
    name: &str,
    param: &Expr,
    itr: &mut dyn Iterator<Item = &Value>,
    mut filters: Value,
) -> Result<Value> {
    loop {
        match itr.next() {
            Some(Value::String(s)) => {
                let mut fc = filters;
                let mut f = &mut fc;
                for p in s.split('/') {
                    let vref = f.make_or_get_value_mut(&[p])?;
                    if *vref == Value::Undefined {
                        *vref = Value::new_object();
                    }
                    f = vref;
                }
                filters = fc;
            }
            Some(Value::Array(a)) => {
                let mut fc = filters;
                let mut f = &mut fc;
                for p in a.iter() {
                    let vref = match f {
                        Value::Object(obj) => {
                            let obj = Rc::make_mut(obj);
                            obj.entry(p.clone()).or_insert_with(Value::new_object)
                        }
                        _ => break,
                    };
                    f = vref;
                }
                filters = fc;
            }
            Some(_) => {
                let span = param.span();
                bail!(span.error(
		    format!("`{name}` requires path to be '/' separated string or array of path components.").as_str()));
            }
            None => break,
        }
    }
    Ok(filters)
}

fn json_filter(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "json.filter";
    ensure_args_count(span, name, params, args, 2)?;
    ensure_object(name, &params[0], args[0].clone())?;

    let filters = match &args[1] {
        Value::Array(a) => merge_filters(name, &params[1], &mut a.iter(), Value::new_object())?,
        Value::Set(s) => merge_filters(name, &params[1], &mut s.iter(), Value::new_object())?,
        _ => bail!(span.error(format!("`{name}` requires set/array argument").as_str())),
    };

    Ok(json_filter_impl(&args[0], &filters))
}

fn filter(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "object.filter";
    ensure_args_count(span, name, params, args, 2)?;
    let mut obj = ensure_object(name, &params[0], args[0].clone())?;
    let obj_ref = Rc::make_mut(&mut obj);
    match &args[1] {
        Value::Array(a) => {
            let keys: BTreeSet<&Value> = a.iter().collect();
            obj_ref.retain(|k, _| keys.contains(k))
        }
        Value::Set(s) => obj_ref.retain(|k, _| s.contains(k)),
        Value::Object(o) => obj_ref.retain(|k, _| o.contains_key(k)),
        _ => bail!(span.error(format!("`{name}` requires array/object/set argument").as_str())),
    };

    Ok(Value::Object(obj))
}

fn get(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "object.get";
    ensure_args_count(span, name, params, args, 3)?;
    let obj = ensure_object(name, &params[0], args[0].clone())?;
    let default = &args[2];

    Ok(match &args[1] {
        Value::Array(keys) => {
            let mut v = &args[0];
            for a in keys.iter() {
                v = &v[a];
                if v == &Value::Undefined {
                    v = default;
                    break;
                }
            }
            v.clone()
        }
        key => match obj.get(key) {
            Some(v) => v.clone(),
            _ => default.clone(),
        },
    })
}

fn keys(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "object.keys";
    ensure_args_count(span, name, params, args, 1)?;
    let obj = ensure_object(name, &params[0], args[0].clone())?;
    Ok(Value::from_set(obj.keys().cloned().collect()))
}

fn remove(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "object.remove";
    ensure_args_count(span, name, params, args, 2)?;
    let mut obj = ensure_object(name, &params[0], args[0].clone())?;
    let obj_ref = Rc::make_mut(&mut obj);
    match &args[1] {
        Value::Array(a) => {
            let keys: BTreeSet<&Value> = a.iter().collect();
            obj_ref.retain(|k, _| !keys.contains(k))
        }
        Value::Set(s) => obj_ref.retain(|k, _| !s.contains(k)),
        Value::Object(o) => obj_ref.retain(|k, _| !o.contains_key(k)),
        _ => bail!(span.error(format!("`{name}` requires array/object/set argument").as_str())),
    };

    Ok(Value::Object(obj))
}

fn is_subset(sup: &Value, sub: &Value) -> bool {
    match (sup, sub) {
        (Value::Object(sup), Value::Object(sub)) => {
            sub.iter().all(|(k, vsub)| {
                match sup.get(k) {
                    //		    Some(vsup @ Value::Object(_)) => is_subset(vsup, vsub),
                    Some(vsup) => is_subset(vsup, vsub),
                    _ => false,
                }
            })
        }
        (Value::Set(sup), Value::Set(sub)) => sub.is_subset(sup),
        (Value::Array(sup), Value::Array(sub)) => sup.windows(sub.len()).any(|w| w == &sub[..]),
        (Value::Array(sup), Value::Set(_)) => {
            let sup = Value::from_set(sup.iter().cloned().collect());
            is_subset(&sup, sub)
        }
        (sup, sub) => sup == sub,
    }
}

fn subset(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "object.subset";
    ensure_args_count(span, name, params, args, 2)?;

    Ok(Value::Bool(is_subset(&args[0], &args[1])))
}
