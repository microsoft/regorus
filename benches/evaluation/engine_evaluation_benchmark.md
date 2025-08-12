# Engine Evaluation Benchmark Results

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
|       1 |                       2.36 |                  423 |
|       2 |                       4.85 |                  412 |
|       4 |                       9.86 |                  406 |
|       6 |                      15.02 |                  399 |
|       8 |                      23.46 |                  341 |
|      10 |                      33.34 |                  300 |
|      12 |                      40.69 |                  295 |
|      14 |                      48.26 |                  290 |
|      16 |                      58.61 |                  273 |
|      18 |                      77.35 |                  233 |
|      20 |                      86.74 |                  231 |
|      22 |                      94.17 |                  234 |
|      24 |                     102.58 |                  234 |
|      26 |                     110.17 |                  236 |
|      28 |                     118.97 |                  235 |
|      30 |                     126.54 |                  237 |
|      32 |                     135.89 |                  235 |

### Cloned Engines, Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                       3.24 |                  309 |
|       2 |                       6.57 |                  304 |
|       4 |                      13.47 |                  297 |
|       6 |                      20.42 |                  294 |
|       8 |                      30.01 |                  266 |
|      10 |                      40.99 |                  244 |
|      12 |                      49.99 |                  240 |
|      14 |                      60.09 |                  233 |
|      16 |                      73.95 |                  216 |
|      18 |                      95.94 |                  188 |
|      20 |                     105.24 |                  190 |
|      22 |                     114.30 |                  192 |
|      24 |                     124.67 |                  193 |
|      26 |                     134.76 |                  193 |
|      28 |                     145.16 |                  193 |
|      30 |                     155.23 |                  193 |
|      32 |                     165.42 |                  193 |

### Fresh Engines, Cloned Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                      17.88 |                   56 |
|       2 |                      36.32 |                   55 |
|       4 |                      74.45 |                   54 |
|       6 |                     112.95 |                   53 |
|       8 |                     150.24 |                   53 |
|      10 |                     189.61 |                   53 |
|      12 |                     228.25 |                   53 |
|      14 |                     297.37 |                   47 |
|      16 |                     373.61 |                   43 |
|      18 |                     426.46 |                   42 |
|      20 |                     477.80 |                   42 |
|      22 |                     523.00 |                   42 |
|      24 |                     570.74 |                   42 |
|      26 |                     619.92 |                   42 |
|      28 |                     670.24 |                   42 |
|      30 |                     717.47 |                   42 |
|      32 |                     748.25 |                   43 |

### Fresh Engines, Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                      18.69 |                   53 |
|       2 |                      38.03 |                   53 |
|       4 |                      77.82 |                   51 |
|       6 |                     118.30 |                   51 |
|       8 |                     157.65 |                   51 |
|      10 |                     197.97 |                   51 |
|      12 |                     239.05 |                   50 |
|      14 |                     310.06 |                   45 |
|      16 |                     391.36 |                   41 |
|      18 |                     441.63 |                   41 |
|      20 |                     495.88 |                   40 |
|      22 |                     543.69 |                   40 |
|      24 |                     591.51 |                   41 |
|      26 |                     645.98 |                   40 |
|      28 |                     697.37 |                   40 |
|      30 |                     749.37 |                   40 |
|      32 |                     784.63 |                   41 |

## Analysis

The benchmark results demonstrate the following performance characteristics with mimalloc as the default allocator:

1. **Best Performance**: Cloned engines with cloned inputs consistently deliver the highest throughput
2. **Configuration Performance Hierarchy**:
   - Cloned engines, cloned inputs: Best performance (optimal configuration)
   - Cloned engines, fresh inputs: ~27% reduction from optimal
   - Fresh engines, cloned inputs: ~87% reduction from optimal
   - Fresh engines, fresh inputs: ~87% reduction from optimal
3. **Scaling Patterns with mimalloc**: 
   - Performance degrades with increased thread count due to contention, but mimalloc provides better thread scaling characteristics
   - Best throughput achieved at 1 thread for cloned engine configurations
   - Fresh engine configurations show poor scaling across all thread counts
   - The use of mimalloc as the default allocator has improved multi-threaded performance and reduced contention
4. **Engine Creation Overhead**: Fresh engine creation is a significant performance bottleneck (~7-8x slower than cloned engines)
5. **Input Processing**: Fresh input generation adds moderate overhead (~27% impact compared to cloned inputs)
6. **Thread Contention**: Performance degradation occurs with higher thread counts across all configurations, though mimalloc helps mitigate some allocation-related contention