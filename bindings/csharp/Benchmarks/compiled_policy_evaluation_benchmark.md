# Compiled Policy Evaluation Benchmark Results (C#/.NET)

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

The C# compiled policy evaluation benchmark tests Regorus compiled policy performance across multiple thread configurations (1-32 threads). It measures throughput (thousands of evaluations per second) for different combinations of compiled policy compilation strategies.

## Configuration Combinations

1. **Compiled Shared Policies**: All threads share pre-compiled policy instances - optimal for performance
2. **Compiled Per Iteration**: Each thread compiles the policy for each evaluation iteration

*Note: The C# implementation uses a simpler configuration model compared to Rust, which also varies input data handling (cloned vs fresh inputs). The C# benchmarks focus on compilation strategies with consistent input handling.*

## Performance Results

### Compiled Shared Policies (Best Performance)
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                    2928.81 |                  211 |
|       2 |                    5892.53 |                  146 |
|       4 |                   11750.71 |                  155 |
|       6 |                   17686.92 |                  134 |
|       8 |                   23543.53 |                   90 |
|      10 |                   29503.80 |                   72 |
|      12 |                   35494.81 |                   58 |
|      14 |                   41408.36 |                   50 |
|      16 |                   47333.65 |                   44 |
|      18 |                   53050.24 |                   38 |
|      20 |                   58807.20 |                   34 |
|      22 |                  406022.45 |                   32 |
|      24 |                   65480.69 |                   32 |
|      26 |                   70952.34 |                   30 |
|      28 |                   72064.03 |                   30 |
|      30 |                  492405.74 |                   27 |
|      32 |                   81210.83 |                   27 |

### Compiled Per Iteration
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                    2984.00 |                   39 |
|       2 |                    5969.45 |                   38 |
|       4 |                   11948.28 |                   32 |
|       6 |                   17927.24 |                   30 |
|       8 |                   23889.01 |                   24 |
|      10 |                   29882.38 |                   20 |
|      12 |                   35865.06 |                   18 |
|      14 |                   41838.70 |                   15 |
|      16 |                   47800.92 |                   14 |
|      18 |                   53257.22 |                   10 |
|      20 |                   59596.93 |                   11 |
|      22 |                  435853.41 |                   10 |
|      24 |                   70870.86 |                    9 |
|      26 |                   76120.59 |                    9 |
|      28 |                   80717.51 |                    8 |
|      30 |                  544207.96 |                    8 |
|      32 |                   91540.91 |                    7 |

## Analysis

The C# compiled policy benchmark demonstrates important performance characteristics:

1. **Compilation Strategy Impact**: Shared compiled policies significantly outperform per-iteration compilation (~5.4x at 1 thread)
2. **Scaling Patterns**: 
   - Best throughput achieved at 1 thread for shared policies
   - Performance generally degrades with increased thread count
3. **Performance Hierarchy**:
   - Shared compiled policies: Best performance (optimal configuration)
   - Per-iteration compilation: ~82% reduction from optimal
4. **Compilation Overhead**: Per-iteration compilation creates substantial overhead, similar to fresh engine creation
5. **Thread Contention**: Significant performance degradation beyond 8 threads for both configurations

## Comparison with Rust Compiled Policy Evaluation

| Configuration    | C# Performance (1 thread)  | Rust Performance (1 thread) | Relative Performance |
|:-----------------|:----------------------------|:-----------------------------|---------------------:|
| Shared Policies  | Best performance            | Higher throughput            |          0.40x-0.70x |
| Per-iteration    | ~82% reduction from optimal | ~85% reduction from optimal  |          0.47x-0.89x |

*Note: Rust benchmarks include additional input data variations (cloned vs fresh inputs) that are not present in the C# implementation.*

## Comparison with C# Engine Evaluation

| Configuration  | Compiled Policy (1 thread) | Engine Evaluation (1 thread) | Performance Ratio |
|:---------------|:----------------------------|:------------------------------|------------------:|
| Optimal Config | Best performance            | Slightly higher throughput    |              0.96x |

## Performance Insights

1. **Compilation Efficiency**: Pre-compiled policies provide massive performance benefits over per-iteration compilation
2. **C# Performance Gap**: C# compiled policies achieve 40%-70% of Rust performance for shared policies
3. **Engine vs Compiled**: In C#, engine evaluation slightly outperforms compiled policies (96%-104% range)

