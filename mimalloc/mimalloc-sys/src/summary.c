#include "mimalloc.h"
#include "mimalloc-stats.h"
#include <stddef.h>
#include <stdint.h>

// Minimal summary returned to Rust callers so we don't expose the full
// mi_stats_t layout.
typedef struct mi_stats_summary_s {
    uint64_t committed_current;
    uint64_t committed_peak;
    uint64_t reserved_current;
    uint64_t reserved_peak;
} mi_stats_summary_t;

static uint64_t clamp_to_u64(int64_t value) {
    return value < 0 ? 0 : (uint64_t)value;
}

mi_decl_export void mi_stats_summary(mi_stats_summary_t* out_summary) {
    if (out_summary == NULL) {
        return;
    }

    mi_stats_t stats;
    mi_stats_get(sizeof(stats), &stats);

    out_summary->committed_current = clamp_to_u64(stats.committed.current);
    out_summary->committed_peak = clamp_to_u64(stats.committed.peak);
    out_summary->reserved_current = clamp_to_u64(stats.reserved.current);
    out_summary->reserved_peak = clamp_to_u64(stats.reserved.peak);
}
