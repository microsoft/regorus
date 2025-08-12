# Comprehensive Multi-Threaded Evaluation Benchmark Results

## Test Environment

### Machine Specifications
- **CPU**: Apple M-series (ARM64 architecture)
- **Physical CPU Cores**: 8 performance cores + 4 efficiency cores
- **Logical CPU Cores**: 16 total (detected by num_cpus)
- **Maximum Threads Tested**: 32 (num_cpus * 2)
- **Memory**: 16+ GB unified memory architecture
- **Operating System**: macOS Sequoia (15.x)
- **Architecture**: ARM64 (Apple Silicon)

### Software Environment
- **Rust Version**: 1.80+ (stable channel, release build with optimizations)
- **Regorus Version**: Latest development build from eval-benchmark branch
- **Benchmark Framework**: Criterion.rs v0.5+
- **Compiler Flags**: `--release` with default optimizations (-O3 equivalent)
- **Target**: `aarch64-apple-darwin`

### Benchmark Configuration
- **Evaluations per Thread**: 1,000 policy evaluations per iteration
- **Warm-up Time**: 3 seconds for statistical stability
- **Measurement Time**: 5-15 seconds (auto-extended for high thread counts)
- **Sample Size**: 100 iterations per measurement (reduced for slow configurations)
- **Statistical Method**: Statistical sampling with outlier detection and filtering

### Policy Complexity
- **Policy Count**: 9 distinct policy types
- **Policy Types**: 
  - RBAC (Role-Based Access Control)
  - Data sensitivity classification
  - Time-based access control
  - Azure VM deployment validation
  - Azure Storage Account security
  - Azure Key Vault access control
  - Azure Network Security Group rules
  - Network security policies
  - Compliance validation
- **Input Variation**: Multiple test cases per policy (3-4 inputs each)
- **Policy Complexity**: Real-world scenarios with complex rule evaluation

## Performance Summary

### Cloned Engines + Cloned Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
| 1       | 10.13                      | 98.71                |
| 2       | 21.89                      | 91.39                |
| 4       | 48.82                      | 81.93                |
| 6       | 77.95                      | 76.98                |
| 8       | 129.67                     | 61.69                |
| 10      | 187.36                     | 53.37                |
| 12      | 261.59                     | 45.87                |
| 14      | 415.43                     | 33.70                |
| 16      | 513.67                     | 31.15                |
| 18      | 619.15                     | 29.07                |
| 20      | 772.09                     | 25.90                |
| 22      | 881.46                     | 24.96                |
| 24      | 1007.0                     | 23.83                |
| 26      | 1131.8                     | 22.97                |
| 28      | 1296.5                     | 21.60                |
| 30      | 1491.8                     | 20.11                |
| 32      | 1671.6                     | 19.14                |

### Cloned Engines + Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
| 1       | 10.89                      | 91.87                |
| 2       | 23.09                      | 86.62                |
| 4       | 48.11                      | 83.14                |
| 6       | 77.53                      | 77.39                |
| 8       | 132.73                     | 60.27                |
| 10      | 205.92                     | 48.56                |
| 12      | 295.64                     | 40.59                |
| 14      | 406.46                     | 34.44                |
| 16      | 532.74                     | 30.03                |
| 18      | 655.55                     | 27.46                |
| 20      | 850.37                     | 23.52                |
| 22      | 1064.2                     | 20.67                |
| 24      | 1295.1                     | 18.53                |
| 26      | 1498.5                     | 17.35                |
| 28      | 1652.3                     | 16.95                |
| 30      | 1861.4                     | 16.12                |
| 32      | 2141.1                     | 14.95                |

### Fresh Engines + Cloned Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
| 1       | 22.72                      | 44.01                |
| 2       | 47.06                      | 42.50                |
| 4       | 104.81                     | 38.17                |
| 6       | 164.79                     | 36.41                |
| 8       | 284.40                     | 28.13                |
| 10      | 435.08                     | 22.98                |
| 12      | 606.11                     | 19.80                |
| 14      | 799.81                     | 17.50                |
| 16      | 925.84                     | 17.28                |
| 18      | 1196.3                     | 15.05                |
| 20      | 1531.6                     | 13.06                |
| 22      | 1752.6                     | 12.55                |
| 24      | 1988.8                     | 12.07                |
| 26      | 2327.5                     | 11.17                |
| 28      | 2695.6                     | 10.39                |
| 30      | 3016.3                     | 9.95                 |
| 32      | 3374.5                     | 9.48                 |

### Fresh Engines + Fresh Inputs
| Threads | Total Evaluation Time (ms) | Throughput (Kelem/s) |
|--------:|---------------------------:|---------------------:|
| 1       | 23.54                      | 42.48                |
| 2       | 51.10                      | 39.14                |
| 4       | 106.89                     | 37.42                |
| 6       | 176.82                     | 33.93                |
| 8       | 280.98                     | 28.47                |
| 10      | 391.73                     | 25.53                |
| 12      | 524.01                     | 22.90                |
| 14      | 707.16                     | 19.80                |
| 16      | 892.45                     | 17.93                |
| 18      | 1126.5                     | 15.98                |
| 20      | 1372.0                     | 14.58                |
| 22      | 1664.4                     | 13.22                |
| 24      | 1867.4                     | 12.85                |
| 26      | 2152.1                     | 12.08                |
| 28      | 2500.5                     | 11.20                |
| 30      | 2924.5                     | 10.26                |
| 32      | 3318.9                     | 9.64                 |

## Key Insights

### Peak Performance Analysis
- **Best Configuration**: Cloned Engines + Cloned Inputs
- **Peak Throughput**: 98.71 Kelem/s at 1 thread
- **Optimal Thread Range**: 1-6 threads for best performance
- **Performance Cliff**: Significant degradation beyond 8 threads

### Thread Scaling Characteristics

#### Performance by Thread Count (Best Configuration)
| Threads | Best Config | Throughput (Kelem/s) | % of Peak Performance |
|--------:|:------------|--------------------:|---------------------:|
| 1       | Cloned/Cloned | 98.71              | 100.0%               |
| 2       | Cloned/Cloned | 91.39              | 92.6%                |
| 4       | Cloned/Fresh  | 83.14              | 84.2%                |
| 6       | Cloned/Fresh  | 77.39              | 78.4%                |
| 8       | Cloned/Cloned | 61.69              | 62.5%                |
| 10      | Cloned/Cloned | 53.37              | 54.1%                |
| 12      | Cloned/Cloned | 45.87              | 46.5%                |
| 16      | Cloned/Cloned | 31.15              | 31.6%                |
| 20      | Cloned/Cloned | 25.90              | 26.2%                |
| 24      | Cloned/Cloned | 23.83              | 24.1%                |
| 32      | Cloned/Cloned | 19.14              | 19.4%                |

### Performance Degradation Analysis

#### Scalability Efficiency
- **Linear Scaling Range**: 1-2 threads (90%+ efficiency)
- **Good Scaling Range**: 2-6 threads (75%+ efficiency)  
- **Poor Scaling Range**: 8+ threads (<65% efficiency)
- **Severe Degradation**: 16+ threads (<35% efficiency)

#### Engine Cloning Impact
- **1 thread**: 2.32x improvement (98.71 vs 42.48 Kelem/s)
- **8 threads**: 2.17x improvement (61.69 vs 28.47 Kelem/s)
- **32 threads**: 1.99x improvement (19.14 vs 9.64 Kelem/s)

#### Input Cloning Impact
- **1 thread**: 7.5% improvement (98.71 vs 91.87 Kelem/s)
- **8 threads**: 2.4% improvement (61.69 vs 60.27 Kelem/s)
- **32 threads**: 28.0% improvement (19.14 vs 14.95 Kelem/s)

## Takeaways

### Optimal Configuration
1. **Always use cloned engines** for 2x+ performance improvement
2. **Enable input cloning** for additional 5-28% performance gain
3. **Avoid high thread counts** (16+) due to severe contention