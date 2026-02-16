---
name: benchmark
description: Run and interpret basin-engines benchmarks (Steel, ember, shale)
model: haiku
---

# Basin Engines Benchmark Skill

Run benchmarks for Steel, ember, and shale engines.

## CRITICAL: Read Before Benchmarking

**ALWAYS read first**: `~/p/basin-bench/docs/BENCHMARK_FAIRNESS.md`

This document contains hard-won lessons about benchmark fairness. Ignoring it leads to misleading claims.

## Pre-Benchmark Checklist

| Check | Why | How |
|-------|-----|-----|
| Read BENCHMARK_FAIRNESS.md | Contains all fairness lessons | `cat ~/p/basin-bench/docs/BENCHMARK_FAIRNESS.md` |
| Use `--batched` for LMDB/redb | 7-24x improvement with proper config | Add `--batched --batch-size 1000` |
| Scale sled cache | Undersized cache = 17x slower | Add `--cache-mb 2048` for 1M+ records |
| Check dataset vs RAM | If data fits in RAM, you're measuring memory | Use larger datasets for I/O testing |

**Note**: Steel uses verify-once checksums (like RocksDB/WiredTiger) - verify on first read from disk, then trust page cache. Use `FileLayoutConfig::fast()` to disable checksums entirely for ZFS/ECC storage.

## Quick Commands

### Steel (Oak engine)

```bash
# Build
cd ~/p/basin-bench && graft build --release -p ycsb-steel

# Single-threaded
ycsb-steel --fast --data-dir /tmp/bench --workload a --records 50000 --ops 200000

# Multi-threaded with sharding
ycsb-steel --fast --shards 64 --threads 4 --data-dir /tmp/bench --workload a --records 50000 --ops 200000

# Ultimate adversarial benchmark (vs sled)
cd ~/p/basin-engines/engines/steel
graft run --release --example ultimate_adversarial
```

### Fair 4-Engine Comparison

```bash
# Use the fair comparison script (includes proper batching for all engines)
RECORDS=50000 OPS=200000 ~/p/basin-bench/scripts/steel-fair-compare.sh
```

### Individual Engine Commands (Fair Config)

```bash
# Steel
ycsb-steel --fast --workload a --records 50000 --ops 200000 --data-dir /tmp/bench

# sled (scaled cache)
ycsb-sled --high-throughput --cache-mb 256 --workload a --records 50000 --ops 200000 --data-dir /tmp/bench

# LMDB (batched + nosync)
ycsb-lmdb --batched --nosync --batch-size 1000 --workload a --records 50000 --ops 200000 --data-dir /tmp/bench

# redb (batched)
ycsb-redb --batched --batch-size 1000 --workload a --records 50000 --ops 200000 --data-dir /tmp/bench
```

## Steel Results (2025-12-23) - Steel Wins All

**Steel now beats LMDB on ALL workloads!**

| Workload | Steel | LMDB | redb | sled | Winner |
|----------|------|------|------|------|--------|
| A (writes) | **2.49M** | 2.24M | 687K | 744K | Steel +11% |
| B (reads) | **3.01M** | 2.90M | 2.05M | 1.55M | Steel +3.8% |
| C (pure read) | **3.03M** | 1.79M | 1.05M | 1.81M | Steel +69% |

### Optimizations That Closed the Gap

**Implemented** (see `docs/STEEL_OPTIMIZATIONS.md`):
- `get_ref()` +8.4% - zero-copy reads (KEY WIN)
- `get_cached_epoch()` +1% - thread-local epoch
- `get_fast()` - seqlock skip (no gain, kept for API)

**Gap closed!** Previous 43% gap on Workload B eliminated via zero-copy optimization.

### Where Steel Actually Wins

| Scenario | Steel Advantage | Notes |
|----------|----------------|-------|
| Write-heavy (Workload A) | 1.07x vs LMDB | COW efficiency |
| Pure reads (Workload C) | 1.52x vs LMDB | Zero-copy mmap |
| Cold reads after restart | 3x vs sled | No log replay |
| Range scans | 3.4x vs sled | COW pages |
| Simplicity | ~6K LOC vs 20K+ | Easier to understand/debug |

### Sharded Write Performance (2025-12-25)

With 64 shards, Steel **beats sled by 2.3x**:

| Writers | Shards | Steel writes/s | vs sled |
|---------|--------|----------------|---------|
| 1 | 16 | 3.0M | 149% |
| 4 | 64 | 10.8M | 230% |
| 8 | 64 | **16.8M** | **237%** |

### Where Steel Does NOT Win

| Scenario | Winner | Notes |
|----------|--------|-------|
| Multi-key transactions | redb/LMDB | Steel has single-key atomicity only |
| 30+ years production hardening | LMDB | Ecosystem maturity |

## Common Mistakes (Avoid These)

| Mistake | What Happens | Fix |
|---------|--------------|-----|
| Benchmark LMDB without `--batched` | 7.9x slower | Use `--batched --batch-size 1000` |
| Benchmark redb without `--batched` | 24x slower | Use `--batched --batch-size 1000` |
| Claim "47x faster than redb" | Misleading | Fair comparison is ~1.9x |
| Small dataset (50MB) | Memory-bound, not I/O | Use 500MB+ for I/O testing |
| Forget to clear between engines | Cache effects | Sleep or clear page cache |

## Key Files

| Purpose | Location |
|---------|----------|
| Steel YCSB | `~/p/basin-bench/engines/ycsb-steel/` |
| Fair script | `~/p/basin-bench/scripts/steel-fair-compare.sh` |
| Fairness docs | `~/p/basin-bench/docs/BENCHMARK_FAIRNESS.md` |
| Steel benchmarks | `~/p/basin-engines/engines/steel/BENCHMARKS.md` |
| **Roadmap to #1** | `~/p/basin-engines/engines/steel/ROADMAP_BEST_KV.md` |
| Ultimate adversarial | `~/p/basin-engines/engines/steel/examples/ultimate_adversarial.rs` |

## Dialectical Improvement

When benchmarking, always ask:
1. "What would a competitor's maintainer criticize about this benchmark?"
2. "Am I using each engine's recommended configuration?"
3. "What am I NOT measuring that matters?"
4. "Is this result surprising? If so, investigate before publishing."
