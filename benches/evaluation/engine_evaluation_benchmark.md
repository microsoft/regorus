# Engine Evaluation Benchmark Results

## Test Environment
- **Platform**: Apple Silicon (M-Series)
- **CPU**: 16 cores
- **Architecture**: ARM64 (aarch64-apple-darwin)
- **Rust Version**: 1.82.0
- **Benchmark Framework**: Criterion.rs
- **Test Data**: 20,000 inputs per evaluation (1000 per thread)
- **Policy**: Complex authorization policy with nested rules

## Benchmark Overview

The engine evaluation benchmark tests Regorus policy evaluation performance across multiple thread configurations (1-32 threads). It measures throughput (thousands of evaluations per second) for different combinations of engine and input data reuse strategies.

## Configuration Combinations

1. **Cloned Engines, Cloned Inputs**: Each thread uses its own engine and clones of parsed input data - optimal for performance
2. **Cloned Engines, Fresh Inputs**: Each thread uses its own engine but parses new inputs each time
3. **Fresh Engines, Cloned Inputs**: Each thread creates a new engine each iteration but reuses input data
4. **Fresh Engines, Fresh Inputs**: Each thread creates new engines and parses new inputs for each iteration

## Performance Results

### Cloned Engines, Cloned Inputs (Best Performance)
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                       3.05 |                  328 |
|       2 |                       7.46 |                  268 |
|       4 |                      16.10 |                  248 |
|       6 |                      25.94 |                  231 |
|       8 |                      50.18 |                  159 |
|      10 |                      80.27 |                  125 |
|      12 |                     106.31 |                  113 |
|      14 |                     137.31 |                  102 |
|      16 |                     163.91 |                   98 |
|      18 |                     182.06 |                   99 |
|      20 |                     191.36 |                  105 |
|      22 |                     201.51 |                  109 |
|      24 |                     217.65 |                  110 |
|      26 |                     228.11 |                  114 |
|      28 |                     248.17 |                  113 |
|      30 |                     264.15 |                  114 |
|      32 |                     314.27 |                  102 |

### Cloned Engines, Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                       4.36 |                  229 |
|       2 |                      10.34 |                  194 |
|       4 |                      21.98 |                  182 |
|       6 |                      34.05 |                  176 |
|       8 |                      66.47 |                  120 |
|      10 |                     100.78 |                   99 |
|      12 |                     141.69 |                   85 |
|      14 |                     188.53 |                   74 |
|      16 |                     261.27 |                   61 |
|      18 |                     285.29 |                   63 |
|      20 |                     312.14 |                   64 |
|      22 |                     329.42 |                   67 |
|      24 |                     347.97 |                   69 |
|      26 |                     370.24 |                   70 |
|      28 |                     394.75 |                   71 |
|      30 |                     419.30 |                   72 |
|      32 |                     433.58 |                   74 |

### Fresh Engines, Cloned Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                      22.39 |                   45 |
|       2 |                      49.22 |                   41 |
|       4 |                      98.09 |                   41 |
|       6 |                     160.21 |                   37 |
|       8 |                     281.26 |                   28 |
|      10 |                     413.61 |                   24 |
|      12 |                     578.15 |                   21 |
|      14 |                     746.34 |                   19 |
|      16 |                     961.44 |                   17 |
|      18 |                    1127.70 |                   16 |
|      20 |                    1248.40 |                   16 |
|      22 |                    1386.90 |                   16 |
|      24 |                    1559.70 |                   15 |
|      26 |                    1736.30 |                   15 |
|      28 |                    1891.80 |                   15 |
|      30 |                    2077.00 |                   14 |
|      32 |                    2289.30 |                   14 |

### Fresh Engines, Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                      23.63 |                   42 |
|       2 |                      48.82 |                   41 |
|       4 |                     102.32 |                   39 |
|       6 |                     160.09 |                   37 |
|       8 |                     271.21 |                   29 |
|      10 |                     397.39 |                   25 |
|      12 |                     489.09 |                   25 |
|      14 |                     670.33 |                   21 |
|      16 |                     884.83 |                   18 |
|      18 |                    1044.00 |                   17 |
|      20 |                    1174.20 |                   17 |
|      22 |                    1330.40 |                   17 |
|      24 |                    1480.90 |                   16 |
|      26 |                    1679.50 |                   15 |
|      28 |                    1873.90 |                   15 |
|      30 |                    2070.90 |                   14 |
|      32 |                    2325.40 |                   14 |

## Analysis

The benchmark results demonstrate the following performance characteristics:

1. **Best Performance**: Cloned engines with cloned inputs consistently deliver the highest throughput
2. **Configuration Performance Hierarchy**:
   - Cloned engines, cloned inputs: Best performance (optimal configuration)
   - Cloned engines, fresh inputs: ~30% reduction from optimal
   - Fresh engines, cloned inputs: ~86% reduction from optimal
   - Fresh engines, fresh inputs: ~87% reduction from optimal
3. **Scaling Patterns**: 
   - Performance degrades with increased thread count due to contention
   - Best throughput achieved at 1 thread for cloned engine configurations
   - Fresh engine configurations show poor scaling across all thread counts
4. **Engine Creation Overhead**: Fresh engine creation is a significant performance bottleneck (~7-8x slower than cloned engines)
5. **Input Processing**: Fresh input generation adds moderate overhead (~30% impact compared to cloned inputs)
6. **Thread Contention**: Performance degradation occurs with higher thread counts across all configurations