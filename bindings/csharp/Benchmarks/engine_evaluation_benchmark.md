# Engine Evaluation Benchmark Results (C#/.NET)

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

The C# engine evaluation benchmark tests Regorus policy evaluation performance across multiple thread configurations (1-32 threads). It measures throughput (thousands of evaluations per second) for different combinations of engine reuse strategies.

## Configuration Combinations

1. **Cloned Engines**: Each thread uses its own cloned engine instance - optimal for performance
2. **Fresh Engines**: Each thread creates a new engine for each evaluation iteration

*Note: The C# implementation uses a simpler configuration model compared to Rust, which also varies input data handling (cloned vs fresh inputs). The C# benchmarks focus on engine reuse strategies with consistent input handling.*

## Performance Results

### Cloned Engines (Best Performance)
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                    2903.43 |                  279 |
|       2 |                    5808.35 |                  227 |
|       4 |                   11645.08 |                  217 |
|       6 |                   17469.69 |                  207 |
|       8 |                   23268.07 |                  114 |
|      10 |                   28996.14 |                  104 |
|      12 |                   34808.60 |                   98 |
|      14 |                   40703.21 |                   72 |
|      16 |                   46488.23 |                   63 |
|      18 |                   52078.52 |                   56 |
|      20 |                   57014.31 |                   51 |
|      22 |                   60482.22 |                   47 |
|      24 |                   62445.67 |                   46 |
|      26 |                   65128.74 |                   45 |
|      28 |                   58001.92 |                   50 |
|      30 |                   66154.78 |                   42 |
|      32 |                   64999.03 |                   45 |

### Fresh Engines
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
|       1 |                    2982.28 |                   50 |
|       2 |                    5962.62 |                   48 |
|       4 |                   11917.94 |                   47 |
|       6 |                   17874.77 |                   46 |
|       8 |                   23729.94 |                   45 |
|      10 |                   29635.17 |                   42 |
|      12 |                   35574.71 |                   38 |
|      14 |                   41482.61 |                   34 |
|      16 |                   47425.16 |                   32 |
|      18 |                   53248.87 |                   29 |
|      20 |                   58424.34 |                   27 |
|      22 |                   61302.24 |                   26 |
|      24 |                   67430.08 |                   23 |
|      26 |                   65226.79 |                   24 |
|      28 |                   73118.48 |                   22 |
|      30 |                  326472.94 |                   23 |
|      32 |                   63805.03 |                   24 |

## Analysis

The C# benchmark results demonstrate important performance characteristics with mimalloc as the default allocator:

1. **Engine Reuse Impact**: Cloned engines significantly outperform fresh engines (~5.6x at 1 thread)
2. **Scaling Patterns with mimalloc**: 
   - Best throughput achieved at 1 thread for both configurations
   - Performance degrades with increased thread count due to contention, but mimalloc provides better allocation efficiency
   - Cloned engines show better relative scaling characteristics
3. **Performance Hierarchy**: 
   - Cloned engines: Best performance (optimal configuration)
   - Fresh engines: ~82% reduction from optimal
4. **Thread Contention**: Significant performance drop beyond 8 threads, especially for fresh engines, though mimalloc helps mitigate some allocation-related issues
5. **C# vs Rust Performance**: C# shows ~66% of Rust performance for equivalent cloned engine configuration

## Comparison with Rust Engine Evaluation

### Multi-Thread Performance Comparison

| Configuration  | 1 Thread (Kelem/s) | 4 Threads (Kelem/s) | 8 Threads (Kelem/s) |
|:---------------|:-------------------|:--------------------|:--------------------|
|                | C# / Rust          | C# / Rust           | C# / Rust           |
| Cloned Engines | 279 / 423          | 217 / 406           | 114 / 341           |
| Fresh Engines  | 50 / 56            | 47 / 54             | 45 / 53             |

### Threading Efficiency Analysis

| Configuration  | Low Contention (1-4t) | Medium Contention (6-12t) | High Contention (16+t) |
|:---------------|:----------------------|:--------------------------|:-----------------------|
|                | Avg C# / Rust         | Avg C# / Rust             | Avg C# / Rust          |
| Cloned Engines | 253 / 414             | 128 / 329                 | 54 / 250               |
| Fresh Engines  | 48 / 55               | 39 / 52                   | 27 / 42                |

**Key Observations:**
- **Single-threaded performance**: C# achieves 66% of Rust performance for cloned engines, 89% for fresh engines
- **Threading scaling**: Both platforms show similar degradation patterns, but Rust maintains better absolute performance
- **Contention resistance**: Fresh engines show more consistent relative performance across thread counts
- **Platform differences**: C# shows more pronounced performance drops at higher thread counts, particularly for cloned engines

*Note: Rust benchmarks include additional input data variations (cloned vs fresh inputs) that are not present in the C# implementation.*

## Performance Insights

1. **Engine Creation Overhead**: Fresh engine creation has significant performance impact in C# (~5.6x slower than cloned engines)
2. **Thread Scaling**: C# shows moderate thread contention with better characteristics when using mimalloc
3. **Memory Management**: .NET garbage collection patterns combined with mimalloc allocation efficiency
4. **Interop Performance**: C# bindings achieve 66% of Rust performance for cloned engines, demonstrating effective FFI implementation
5. **mimalloc Benefits**: The use of mimalloc as the default allocator in the underlying Rust FFI provides improved memory allocation efficiency and better threading characteristics

