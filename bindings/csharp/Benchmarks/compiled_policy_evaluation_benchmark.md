# Compiled Policy Evaluation Benchmark Results (C#/.NET)

## Test Environment
- **Platform**: Apple Silicon (M-Series)
- **CPU**: 16 cores
- **Architecture**: ARM64 (aarch64-apple-darwin)
- **.NET Version**: 8.0
- **Allocator**: mimalloc (default allocator for Rust FFI)
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
|       1 |                    2905.41 |                  273 |
|       2 |                    5808.07 |                  240 |
|       4 |                   11631.23 |                  227 |
|       6 |                   17431.95 |                  216 |
|       8 |                   23183.42 |                  126 |
|      10 |                   28886.11 |                  118 |
|      12 |                   34659.87 |                  108 |
|      14 |                   40564.07 |                   84 |
|      16 |                   46446.38 |                   72 |
|      18 |                   52047.06 |                   63 |
|      20 |                   56983.45 |                   58 |
|      22 |                  404931.47 |                   55 |
|      24 |                   61673.71 |                   55 |
|      26 |                   64370.41 |                   51 |
|      28 |                   56897.04 |                   59 |
|      30 |                  406850.06 |                   52 |
|      32 |                   56786.24 |                   58 |

### Compiled Per Iteration
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                    2978.06 |                   49 |
|       2 |                    5965.09 |                   47 |
|       4 |                   11928.23 |                   46 |
|       6 |                   17892.58 |                   45 |
|       8 |                   23773.82 |                   43 |
|      10 |                   29705.61 |                   42 |
|      12 |                   35631.97 |                   40 |
|      14 |                   41563.35 |                   34 |
|      16 |                   47452.93 |                   31 |
|      18 |                   53505.42 |                   27 |
|      20 |                   59393.86 |                   25 |
|      22 |                  436115.28 |                   23 |
|      24 |                   71088.08 |                   21 |
|      26 |                   76928.70 |                   19 |
|      28 |                   82759.27 |                   18 |
|      30 |                  560658.97 |                   17 |
|      32 |                   93949.39 |                   16 |

## Analysis

The C# compiled policy benchmark demonstrates important performance characteristics with mimalloc as the default allocator:

1. **Compilation Strategy Impact**: Shared compiled policies significantly outperform per-iteration compilation (~5.6x at 1 thread)
2. **Scaling Patterns with mimalloc**: 
   - Best throughput achieved at 1 thread for shared policies
   - Performance generally degrades with increased thread count, but mimalloc provides better allocation efficiency
3. **Performance Hierarchy**:
   - Shared compiled policies: Best performance (optimal configuration)
   - Per-iteration compilation: ~82% reduction from optimal
4. **Compilation Overhead**: Per-iteration compilation creates substantial overhead, similar to fresh engine creation
5. **Thread Contention**: Significant performance degradation beyond 8 threads for both configurations, though mimalloc helps mitigate some allocation-related issues

## Comparison with Rust Compiled Policy Evaluation

### Multi-Thread Performance Comparison

| Configuration    | 1 Thread (Kelem/s) | 4 Threads (Kelem/s) | 8 Threads (Kelem/s) |
|:-----------------|:-------------------|:--------------------|:--------------------|
|                  | C# / Rust          | C# / Rust           | C# / Rust           |
| Shared Policies  | 273 / 426          | 227 / 342           | 126 / 185           |
| Per-iteration    | 49 / 55            | 46 / 50             | 43 / 50             |

### Threading Efficiency Analysis

| Configuration    | Low Contention (1-4t) | Medium Contention (6-12t) | High Contention (16+t) |
|:-----------------|:----------------------|:--------------------------|:-----------------------|
|                  | Avg C# / Rust         | Avg C# / Rust             | Avg C# / Rust          |
| Shared Policies  | 249 / 384             | 150 / 203                 | 58 / 123               |
| Per-iteration    | 47 / 54               | 40 / 50                   | 22 / 42                |

**Key Observations:**
- **Single-threaded performance**: C# achieves 64% of Rust performance for shared policies, 89% for per-iteration
- **Threading scaling**: Both platforms show similar degradation patterns, but Rust maintains better absolute performance
- **Contention resistance**: Per-iteration compilation shows more consistent relative performance across thread counts
- **Platform differences**: C# shows more pronounced performance drops at higher thread counts, particularly for shared policies

*Note: Rust benchmarks include additional input data variations (cloned vs fresh inputs) that are not present in the C# implementation.*

## Comparison with C# Engine Evaluation

### Multi-Thread Performance Comparison

| Configuration   | 1 Thread (Kelem/s) | 4 Threads (Kelem/s) | 8 Threads (Kelem/s) |
|:----------------|:-------------------|:--------------------|:--------------------|
|                 | CP / EE            | CP / EE             | CP / EE             |
| Shared Policies | 273 / 279          | 227 / 217           | 126 / 114           |
| Per-iteration   | 49 / 50            | 46 / 47             | 43 / 45             |

### Threading Efficiency Analysis

| Configuration   | Low Contention (1-4t) | Medium Contention (6-12t) | High Contention (16+t) |
|:----------------|:----------------------|:--------------------------|:-----------------------|
|                 | Avg CP / EE           | Avg CP / EE               | Avg CP / EE            |
| Shared Policies | 249 / 248             | 150 / 128                 | 58 / 54                |
| Per-iteration   | 47 / 48               | 40 / 39                   | 22 / 27                |

**Key Observations:**
- **Single-threaded parity**: Both systems perform nearly identically at 1 thread
- **Threading behavior**: Compiled policies slightly outperform engine evaluation at higher thread counts for shared policies
- **Contention resistance**: Per-iteration configurations show very similar performance characteristics across all thread counts
- **Platform consistency**: Both C# implementations show similar scaling patterns and contention behavior

## Performance Insights

1. **C# vs Rust Performance**: C# compiled policies achieve 65% average performance of Rust for shared policies, 87% average for per-iteration across low contention scenarios
2. **Engine vs Compiled**: In C#, engine and compiled policy evaluation show very similar average performance (compiled policies achieve 100% of engine performance for shared policies, 98% for per-iteration)
3. **mimalloc Impact**: The use of mimalloc as the default allocator in the underlying Rust FFI provides better memory allocation efficiency and improved threading characteristics
4. **Threading Scaling**: Both C# configurations demonstrate similar contention patterns, with shared policies showing more pronounced degradation under high thread contention compared to per-iteration compilation

