# Compiled Policy Evaluation Benchmark Results

## Test Environment
- **Platform**: Apple Silicon (M-Series)
- **CPU**: 16 cores
- **Architecture**: ARM64 (aarch64-apple-darwin)
- **Rust Version**: 1.82.0
- **Allocator**: mimalloc (default allocator)
- **Benchmark Framework**: Criterion.rs
- **Test Data**: 20,000 inputs per evaluation (1000 per thread)
- **Policy**: Complex authorization policy with nested rules

## Benchmark Overview

The compiled policy evaluation benchmark tests Regorus compiled policy performance across multiple thread configurations (1-32 threads). It measures throughput (thousands of evaluations per second) for different combinations of compiled policy and input data reuse strategies.

## Configuration Combinations

1. **Compiled Shared Policies, Cloned Inputs**: Each thread uses shared compiled policies and clones of parsed input data - optimal for performance
2. **Compiled Shared Policies, Fresh Inputs**: Each thread uses shared compiled policies but parses new inputs each time
3. **Compiled Per Iteration, Cloned Inputs**: Each thread compiles the policy each iteration but reuses input data
4. **Compiled Per Iteration, Fresh Inputs**: Each thread compiles new policies and parses new inputs for each iteration

## Performance Results

### Compiled Shared Policies, Cloned Inputs (Best Performance)
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                       2.35 |                  426 |
|       2 |                       5.36 |                  373 |
|       4 |                      11.70 |                  342 |
|       6 |                      20.33 |                  295 |
|       8 |                      43.26 |                  185 |
|      10 |                      61.93 |                  162 |
|      12 |                      79.30 |                  151 |
|      14 |                      94.45 |                  148 |
|      16 |                     113.39 |                  141 |
|      18 |                     154.41 |                  117 |
|      20 |                     184.37 |                  108 |
|      22 |                     204.00 |                  108 |
|      24 |                     220.45 |                  109 |
|      26 |                     237.07 |                  110 |
|      28 |                     252.58 |                  111 |
|      30 |                     273.57 |                  110 |
|      32 |                     292.69 |                  109 |

### Compiled Shared Policies, Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                       3.34 |                  299 |
|       2 |                       7.29 |                  274 |
|       4 |                      15.19 |                  263 |
|       6 |                      24.90 |                  241 |
|       8 |                      49.22 |                  163 |
|      10 |                      68.45 |                  146 |
|      12 |                      86.55 |                  139 |
|      14 |                     104.77 |                  134 |
|      16 |                     136.07 |                  118 |
|      18 |                     169.05 |                  106 |
|      20 |                     198.25 |                  101 |
|      22 |                     217.05 |                  101 |
|      24 |                     234.75 |                  102 |
|      26 |                     254.53 |                  102 |
|      28 |                     276.06 |                  101 |
|      30 |                     296.12 |                  101 |
|      32 |                     318.81 |                  100 |

### Compiled Per Iteration, Cloned Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                      18.11 |                   55 |
|       2 |                      36.89 |                   54 |
|       4 |                      75.46 |                   53 |
|       6 |                     114.66 |                   52 |
|       8 |                     152.80 |                   52 |
|      10 |                     192.17 |                   52 |
|      12 |                     232.32 |                   52 |
|      14 |                     301.47 |                   46 |
|      16 |                     380.36 |                   42 |
|      18 |                     424.64 |                   42 |
|      20 |                     484.76 |                   41 |
|      22 |                     531.62 |                   41 |
|      24 |                     582.88 |                   41 |
|      26 |                     631.39 |                   41 |
|      28 |                     671.99 |                   42 |
|      30 |                     717.65 |                   42 |
|      32 |                     766.05 |                   42 |

### Compiled Per Iteration, Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                      19.07 |                   52 |
|       2 |                      38.89 |                   51 |
|       4 |                      79.52 |                   50 |
|       6 |                     120.89 |                   50 |
|       8 |                     161.08 |                   50 |
|      10 |                     202.37 |                   49 |
|      12 |                     244.04 |                   49 |
|      14 |                     316.66 |                   44 |
|      16 |                     398.02 |                   40 |
|      18 |                     449.54 |                   40 |
|      20 |                     500.57 |                   40 |
|      22 |                     557.97 |                   39 |
|      24 |                     605.71 |                   40 |
|      26 |                     656.88 |                   40 |
|      28 |                     710.03 |                   39 |
|      30 |                     741.09 |                   40 |
|      32 |                     801.26 |                   40 |

## Analysis

The compiled policy benchmark demonstrates the following performance characteristics with mimalloc as the default allocator:

1. **Best Performance**: Compiled shared policies with cloned inputs provide the highest throughput
2. **Compilation Impact**: 
   - Pre-compiled policies: Significantly faster than per-iteration compilation
   - Per-iteration compilation: Major overhead (~7-8x slower than pre-compiled)
3. **Scaling Patterns with mimalloc**:
   - Best throughput achieved at 1 thread for shared policy configurations
   - mimalloc provides better thread scaling characteristics compared to the default allocator
   - Higher thread counts show performance degradation due to contention, but less severe with mimalloc
   - Per-iteration compilation shows poor scaling across all thread counts
4. **Input Processing**: Fresh inputs add ~30% overhead across all configurations
5. **Thread Performance with mimalloc**: 
   - Peak performance at 1 thread for most configurations
   - Reasonable performance maintained up to 12-16 threads for shared policies
   - Compiled policies show better thread scaling than per-iteration compilation
   - mimalloc helps reduce allocation-related contention in multi-threaded scenarios

## Comparison with Engine Evaluation

### Multi-Thread Performance Comparison

| Configuration        | 1 Thread (Kelem/s) | 4 Threads (Kelem/s) | 8 Threads (Kelem/s) |
|:---------------------|:-------------------|:--------------------|:--------------------|
|                      | CP / EE            | CP / EE             | CP / EE             |
| Shared/Cloned        | 426 / 423          | 342 / 406           | 185 / 341           |
| Shared/Fresh         | 299 / 309          | 263 / 297           | 163 / 266           |
| Per-iteration/Cloned | 55 / 56            | 53 / 54             | 52 / 53             |
| Per-iteration/Fresh  | 52 / 53            | 50 / 51             | 50 / 51             |

### Threading Efficiency Analysis

| Configuration        | Low Contention (1-4t) | Medium Contention (6-12t) | High Contention (16+t) |
|:---------------------|:----------------------|:--------------------------|:-----------------------|
|                      | Avg CP / EE           | Avg CP / EE               | Avg CP / EE            |
| Shared/Cloned        | 384 / 414             | 203 / 329                 | 123 / 250              |
| Shared/Fresh         | 284 / 302             | 176 / 235                 | 108 / 201              |
| Per-iteration/Cloned | 54 / 55               | 50 / 52                   | 42 / 42                |
| Per-iteration/Fresh  | 51 / 52               | 47 / 50                   | 40 / 40                |

The compiled policy evaluation shows performance characteristics that are generally comparable to engine evaluation, though with some notable differences. While single-threaded performance is very close between the systems, there are observable impacts from the compilation approach that become more apparent under different threading scenarios.

**Key Observations:**
- **Single-threaded performance**: Very close parity between systems, though results may vary between runs
- **Threading behavior**: Engine evaluation demonstrates better scaling characteristics under higher thread contention (4+ threads)
- **Multi-threaded impact**: Compiled policies show more pronounced performance degradation under thread contention in shared policy configurations
- **Contention resistance**: Per-iteration compilation shows more consistent (though lower absolute) performance across thread counts
- **Optimal usage**: Both systems achieve best results with minimal threading (1-4 threads), though engine evaluation maintains better performance at higher thread counts for shared configurations

