# Engine Evaluation Benchmark Results (C#/.NET)

## Test Environment
- **Platform**: Apple Silicon (M-Series)
- **CPU**: 16 cores
- **Architecture**: ARM64 (aarch64-apple-darwin)
- **.NET Version**: 8.0
- **Benchmark Framework**: Custom time-based benchmarking
- **Test Data**: 20,000 inputs per evaluation (distributed across threads)
- **Policy**: Complex authorization policy with nested rules
- **Warmup Duration**: 3 seconds per configuration
- **Evaluation Duration**: 3 seconds per configuration

## Benchmark Overview

The C# engine evaluation benchmark tests Regorus policy evaluation performance across multiple thread configurations (1-32 threads). It measures throughput (thousands of evaluations per second) for different combinations of engine reuse strategies.

## Configuration Combinations

1. **Cloned Engines**: Each thread uses its own cloned engine instance - optimal for performance
2. **Fresh Engines**: Each thread creates a new engine for each evaluation iteration

*Note: The C# implementation uses a simpler configuration model compared to Rust, which also varies input data handling (cloned vs fresh inputs). The C# benchmarks focus on engine reuse strategies with consistent input handling.*

## Performance Results

### Cloned Engines (Best Performance)
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                    2930.56 |                  219 |
|       2 |                    5868.46 |                  177 |
|       4 |                   11771.01 |                  146 |
|       6 |                   17682.52 |                  129 |
|       8 |                   23633.65 |                   78 |
|      10 |                   29489.12 |                   67 |
|      12 |                   35455.23 |                   57 |
|      14 |                   41353.65 |                   47 |
|      16 |                   47378.91 |                   42 |
|      18 |                   52750.68 |                   36 |
|      20 |                   58131.31 |                   35 |
|      22 |                   62964.88 |                   31 |
|      24 |                   64337.75 |                   34 |
|      26 |                   70044.96 |                   29 |
|      28 |                   72553.98 |                   28 |
|      30 |                   79323.25 |                   26 |
|      32 |                   78624.33 |                   26 |

### Fresh Engines
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                    2985.49 |                   41 |
|       2 |                    5968.13 |                   38 |
|       4 |                   11942.10 |                   34 |
|       6 |                   17918.75 |                   32 |
|       8 |                   23873.57 |                   25 |
|      10 |                   29863.85 |                   20 |
|      12 |                   35823.98 |                   19 |
|      14 |                   41811.53 |                   16 |
|      16 |                   47819.89 |                   14 |
|      18 |                   53478.32 |                   13 |
|      20 |                   59191.93 |                   12 |
|      22 |                   64630.71 |                   11 |
|      24 |                   70215.54 |                   10 |
|      26 |                   75732.06 |                    9 |
|      28 |                   80897.59 |                    9 |
|      30 |                  949904.84 |                    8 |
|      32 |                   92592.64 |                    8 |

## Analysis

The C# benchmark results demonstrate important performance characteristics:

1. **Engine Reuse Impact**: Cloned engines significantly outperform fresh engines (~5.3x at 1 thread)
2. **Scaling Patterns**: 
   - Best throughput achieved at 1 thread for both configurations
   - Performance degrades with increased thread count due to contention
   - Cloned engines show better relative scaling characteristics
3. **Performance Hierarchy**: 
   - Cloned engines: Best performance (optimal configuration)
   - Fresh engines: ~81% reduction from optimal
4. **Thread Contention**: Significant performance drop beyond 8 threads, especially for fresh engines
5. **C# vs Rust Performance**: C# shows ~67% of Rust performance for equivalent cloned engine configuration

## Comparison with Rust Engine Evaluation

| Configuration  | C# Performance (1 thread) | Rust Performance (1 thread) | Relative Performance |
|:---------------|:---------------------------|:-----------------------------|---------------------:|
| Cloned Engines | Best performance           | Higher throughput            |          0.67x-0.92x |
| Fresh Engines  | ~81% reduction from optimal| ~87% reduction from optimal  |          0.75x-0.95x |

*Note: Rust benchmarks include additional input data variations (cloned vs fresh inputs) that are not present in the C# implementation.*

## Performance Insights

1. **Engine Creation Overhead**: Fresh engine creation has massive performance impact in C# (~5.3x slower)
2. **Thread Scaling**: C# shows more significant thread contention than Rust implementation
3. **Memory Management**: .NET garbage collection may contribute to performance variations
4. **Interop Overhead**: C# bindings add measurable overhead compared to native Rust

