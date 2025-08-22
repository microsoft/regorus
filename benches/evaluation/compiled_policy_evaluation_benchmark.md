# Compiled Policy Evaluation Benchmark Results

## Test Environment
- **Platform**: Apple Silicon (M-Series)
- **CPU**: 16 cores
- **Architecture**: ARM64 (aarch64-apple-darwin)
- **Rust Version**: 1.82.0
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
|       1 |                       3.30 |                  303 |
|       2 |                       8.53 |                  234 |
|       4 |                      18.78 |                  213 |
|       6 |                      32.35 |                  186 |
|       8 |                      73.12 |                  109 |
|      10 |                     108.97 |                   92 |
|      12 |                     145.56 |                   82 |
|      14 |                     196.14 |                   71 |
|      16 |                     248.77 |                   64 |
|      18 |                     290.01 |                   62 |
|      20 |                     317.16 |                   63 |
|      22 |                     348.83 |                   63 |
|      24 |                     361.05 |                   66 |
|      26 |                     389.70 |                   67 |
|      28 |                     418.66 |                   67 |
|      30 |                     444.40 |                   68 |
|      32 |                     476.53 |                   67 |

### Compiled Shared Policies, Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                       4.51 |                  222 |
|       2 |                       9.77 |                  205 |
|       4 |                      23.36 |                  171 |
|       6 |                      38.12 |                  157 |
|       8 |                      85.02 |                   94 |
|      10 |                     133.66 |                   75 |
|      12 |                     180.46 |                   66 |
|      14 |                     238.23 |                   59 |
|      16 |                     318.78 |                   50 |
|      18 |                     353.15 |                   51 |
|      20 |                     389.29 |                   51 |
|      22 |                     459.61 |                   48 |
|      24 |                     507.62 |                   47 |
|      26 |                     539.43 |                   48 |
|      28 |                     554.99 |                   50 |
|      30 |                     625.57 |                   48 |
|      32 |                     690.55 |                   46 |

### Compiled Per Iteration, Cloned Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                      22.68 |                   44 |
|       2 |                      47.99 |                   42 |
|       4 |                     108.09 |                   37 |
|       6 |                     167.62 |                   36 |
|       8 |                     283.17 |                   28 |
|      10 |                     418.25 |                   24 |
|      12 |                     546.24 |                   22 |
|      14 |                     688.79 |                   20 |
|      16 |                     951.72 |                   17 |
|      18 |                    1060.20 |                   17 |
|      20 |                    1223.60 |                   16 |
|      22 |                    1342.50 |                   16 |
|      24 |                    1445.70 |                   17 |
|      26 |                    1676.50 |                   15 |
|      28 |                    1765.20 |                   16 |
|      30 |                    1939.00 |                   15 |
|      32 |                    2197.30 |                   15 |

### Compiled Per Iteration, Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                      23.95 |                   42 |
|       2 |                      49.53 |                   40 |
|       4 |                     116.42 |                   34 |
|       6 |                     197.35 |                   30 |
|       8 |                     293.04 |                   27 |
|      10 |                     385.90 |                   26 |
|      12 |                     508.82 |                   24 |
|      14 |                     679.23 |                   21 |
|      16 |                     913.02 |                   18 |
|      18 |                    1075.90 |                   17 |
|      20 |                    1209.80 |                   17 |
|      22 |                    1358.90 |                   16 |
|      24 |                    1523.90 |                   16 |
|      26 |                    1700.20 |                   15 |
|      28 |                    1966.90 |                   14 |
|      30 |                    2179.30 |                   14 |
|      32 |                    2327.70 |                   14 |

## Analysis

The compiled policy benchmark demonstrates the following performance characteristics:

1. **Best Performance**: Compiled shared policies with cloned inputs provide the highest throughput
2. **Compilation Impact**: 
   - Pre-compiled policies: Significantly faster than per-iteration compilation
   - Per-iteration compilation: Major overhead (~7x slower than pre-compiled)
3. **Scaling Patterns**:
   - Best throughput achieved at 1 thread for shared policy configurations
   - Higher thread counts show performance degradation due to contention
   - Per-iteration compilation shows poor scaling across all thread counts
4. **Input Processing**: Fresh inputs add ~25-30% overhead across all configurations
5. **Thread Performance**: 
   - Peak performance at 1 thread for most configurations
   - Reasonable performance maintained up to 12-16 threads for shared policies
   - Compiled policies show better thread scaling than per-iteration compilation

## Comparison with Engine Evaluation

| Configuration        | Compiled Policy (1 thread)      | Engine Evaluation (1 thread)    | Performance Ratio |
|:---------------------|:--------------------------------|:--------------------------------|------------------:|
| Shared/Cloned        | Best performance                | Higher throughput               |       0.67x-0.92x |
| Shared/Fresh         | ~27% reduction from optimal     | ~30% reduction from optimal     |       0.62x-0.97x |
| Per-iteration/Cloned | ~85% reduction from optimal     | ~86% reduction from optimal     |       0.80x-0.98x |
| Per-iteration/Fresh  | ~86% reduction from optimal     | ~87% reduction from optimal     |       0.78x-1.00x |

