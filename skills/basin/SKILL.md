---
name: basin
description: "Basin unified storage platform. Rust monorepo with Sigil language, GPU pipelines, and multi-engine storage. Use when working in the basin codebase."
metadata:
  trit: 1
  version: "0.1.0"
  bundle: infrastructure
---

# Basin Skill

**Repo**: `/Users/alice/worlds/b/basin` (jj + git@github.com:zubyul/basin.git)
**Full context**: `docs/BASIN_CONTEXT_20K.md`

## Build & Test

```bash
cd /Users/alice/worlds/b/basin
graft build --release
graft test --workspace          # uses nextest
graft run -p basin --release    # run basind
```

## Repo Layout

```
foundation/    # Zero-dep crates: core-traits, basin-error, basin-par
engines/       # scree (hash), steel (btree), shale (LSM), sonar (HNSW)
crates/        # Core: slate, spiel, magma, shore, shoal, dgx-sim
modules/       # Protocol modules (dynamic loading)
apps/          # basin-redis, basin-s3, etc.
products/      # Unified binaries: basin, yard, graft-daemon
sigil/         # Sigil language + compiler
tools/         # refactor, forge, semantic-git
warehouse_map/ # DGX fabric topology, Modelica sim, network SVGs
cli/           # basin-cli, basin-shell
```

## Engines

| Engine | Type | Use |
|--------|------|-----|
| Scree | Hash | Hot L0, O(1), 3M+ ops/s |
| Steel | B-tree | Ordered L1, range scans |
| Shale | LSM | Cold storage, write-heavy |
| Sonar | HNSW | ANN search |

CAS integrated into Slate via `SlateContentStore`.

## Sigil Language

```bash
graft run --bin sigil --features rust-codegen -- file.sigil --gpu=compile
graft run --bin sigil --features rust-codegen -- file.sigil --gpu=run
graft run --bin sigil --features rust-codegen -- --gpu=info
```

## DGX Simulator

```bash
graft test -p dgx-sim           # test cycle-level sim
graft bench -p dgx-sim          # benchmarks
```

Crate at `crates/dgx-sim/` — cycle-level GB10 simulator with tropical semiring cost algebra.

## Warehouse Map

`warehouse_map/` contains the physical DGX Spark cluster topology:
- 11 DGX Spark machines via CRS812 switch (1.2 Tb/s fabric)
- `Warehouse.mo` — Modelica acausal model (WiFi L1 + fabric L2)
- `simulate.py` — DAE solver outputting to DuckDB
- `WarehouseNetwork.svg` — integrated topology diagram
- `warehouse.duckdb` — all simulation + tailscale mesh data

## Version Control

```bash
cd /Users/alice/worlds/b/basin
jj st                              # status
jj describe -m "msg"               # commit message
jj git push --bookmark main        # push
jj git fetch && jj rebase -d main@origin  # pull + rebase
```
