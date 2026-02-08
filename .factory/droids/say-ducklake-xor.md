---
name: say-ducklake-xor
description: Parallel thread/DuckLake discovery with XOR uniqueness from gay_seed. Finds "say" or MCP usage, cross-refs with all DuckDB sources, launches bounded parallel ops.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Say-DuckLake XOR Discovery

**Maximally parallel discovery with deterministic uniqueness guarantees.**

## Core Invariants

```
∀ i,j ∈ [0, bound): i ≠ j ⟹ seed ⊕ i ≠ seed ⊕ j   (XOR uniqueness)
∀ parallel ops: same gay_seed ⟹ same colors        (SPI guarantee)
Σ(trits) ≡ 0 (mod 3)                                (GF(3) conservation)
```

## Usage

```bash
# Find all "say" usage in threads, cross-ref with DuckLakes
python scripts/say_ducklake_xor.py

# With explicit seed and parallelism bound
python scripts/say_ducklake_xor.py --seed 1069 --bound 27

# XOR verification mode
python scripts/say_ducklake_xor.py --verify-xor
```

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    gay_seed (root)                          │
├─────────────────────────────────────────────────────────────┤
│  XOR Fan-Out (bounded)                                      │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐     ┌─────────┐       │
│  │seed⊕0   │ │seed⊕1   │ │seed⊕2   │ ... │seed⊕n-1 │       │
│  │(thread) │ │(duck_0) │ │(duck_1) │     │(duck_n) │       │
│  └────┬────┘ └────┬────┘ └────┬────┘     └────┬────┘       │
│       │           │           │               │             │
│       ▼           ▼           ▼               ▼             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              Parallel Executor (async)               │   │
│  │  - Thread search: find_thread("say" OR "say mcp")   │   │
│  │  - DuckDB scan: SHOW TABLES for each .duckdb        │   │
│  │  - Cross-reference: match concepts/timestamps       │   │
│  └─────────────────────────────────────────────────────┘   │
│                           │                                 │
│                           ▼                                 │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              GF(3) Conservation Check                │   │
│  │  Σ(trits) mod 3 = 0 ⟹ valid parallel merge         │   │
│  └────────