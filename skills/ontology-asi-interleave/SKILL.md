---
name: ontology-asi-interleave
description: >
  Bridge connecting plurigrid/ontology to ASI skill graph. Wires autopoietic
  ergodicity, Open Games, Gromov-Wasserstein theory, Arena CRDT, Nexus Nodes,
  and transactive energy into decentralized energy coordination, digital twin
  multi-agent systems, and grid intelligence. Use when connecting ontology
  concepts to ASI skills, designing transactive energy markets, or bridging
  Arena CRDT to DuckDB.
---

# Ontology x ASI Interleave

Bridge connecting `plurigrid/ontology` (the Plurigrid protocol's mathematical and systems foundation) to the ASI skill graph.

## plurigrid/ontology -- 7 Core Concepts

```
1. Autopoietic Ergodicity    -- self-org + time-avg = ensemble-avg convergence
2. Open Games Framework      -- compositional game theory, Markov categories
3. Gromov-Wasserstein Theory  -- metric measure space comparison, entropic reg.
4. Arena System              -- local-first graph DB, Rust + Yrs CRDTs, DuckDB
5. Digital Twin Architecture -- multi-agent value elicitation, mutual recursion
6. Nexus Nodes               -- 3-tier hardware: Apple Silicon / RPi4 / Pico W
7. Transactive Energy        -- stigmergic markets, multi-agent RL + Open Games
```

## Integration Points

### 1. Autopoietic Ergodicity <-> autopoiesis, ergodicity, dynamic-sufficiency

A system that self-organizes (autopoiesis) such that time averages equal ensemble averages (ergodicity), minimizing surprise through continuous learning (active inference).

`dynamic-sufficiency` (145 references, central hub) is the primary landing point. Ontology's "embodied gradualism" maps to dynamic-sufficiency's gradual capability accumulation.

### 2. Open Games Framework <-> open-games, cybernetic-open-game

The Plurigrid protocol IS a compositional open game. Agents are morphisms in a Markov category with generative (play) and recognition (coplay) channels.

Grid = composed game: `node_game @ transmission_game @ market_game`. The correlated equilibrium = autopoietically ergodic state = Nash equilibrium that is also thermodynamically stable.

### 3. Gromov-Wasserstein Theory <-> gflownet, duckdb-spatial

GW theory compares metric measure spaces and does graph matching across heterogeneous energy networks. Entropic regularization + Bregman projections for efficient optimization. GFlowNet samples from energy-proportional distributions over combinatorial structures -- the same optimal transport problem that GW solves for network matching.

### 4. Arena CRDT System <-> crdt, time-travel-crdt, duckdb-ies

Arena is a local-first graph-based data store in Rust with DuckDB backend and Yrs CRDTs for real-time peer synchronization.

Arena schema: `nodes(id, label, properties)` + `edges(id, src, dst, label, properties)` -- maps directly to DuckDB graph patterns.

### 5. Digital Twin Architecture <-> dynamic-sufficiency, agent-o-rama

The digital twin's active inference loop (predict -> act -> observe -> update) is the same loop that `dynamic-sufficiency` implements for ASI skill selection.

### 6. Nexus Nodes <-> hvm-runtime, world-runtime, iot-device-provisioning

3-tier hardware architecture targeting wasm32-unknown-unknown with WASI + capability plugins:

| Tier | Hardware | Compute | ASI Skill |
|---|---|---|---|
| High Power | Apple Silicon (M-series) | Full WASM + TF ext. | hvm-runtime |
| Low Power | Raspberry Pi 4 (4GB ARM) | WASI core | iot-device-provisioning |
| Embedded | RPi Pico W (264KB SRAM) | Minimal WASI | iot-device-provisioning |

Runtime: WasmEdge for high-perf WASM with TensorFlow extensions.

### 7. Transactive Energy <-> nashator, open-games, equilibrium

Market-based transactions between energy grids. Stigmergic feedback for energy availability, demand, and prices.

Nashator at 127.0.0.1:9999 is the direct implementation target: each energy node submits bids as open game moves, the Nashator resolves to correlated equilibrium = market clearing price.

## Concrete Affordances

### Arena CRDT Schema in DuckDB

Create the Arena graph schema and insert sample energy-grid nodes:

```sql
-- File: /Users/alice/v/asi/skills/ontology-asi-interleave/arena_schema.sql
-- Run: duckdb /Users/alice/v/arena.duckdb < arena_schema.sql

CREATE TABLE IF NOT EXISTS arena_nodes (
    id        VARCHAR PRIMARY KEY,
    label     VARCHAR NOT NULL,
    properties JSON,
    created_at TIMESTAMP DEFAULT current_timestamp,
    yrs_clock  BIGINT DEFAULT 0  -- Yrs CRDT logical clock
);

CREATE TABLE IF NOT EXISTS arena_edges (
    id    VARCHAR PRIMARY KEY,
    src   VARCHAR NOT NULL REFERENCES arena_nodes(id),
    dst   VARCHAR NOT NULL REFERENCES arena_nodes(id),
    label VARCHAR NOT NULL,
    properties JSON,
    weight DOUBLE DEFAULT 1.0
);

-- Sample: three Nexus Nodes forming a transactive energy triangle
INSERT OR IGNORE INTO arena_nodes VALUES
  ('nexus-m4',  'apple-silicon', '{"tier":"high","watt_capacity":150}',  now(), 1),
  ('nexus-rpi', 'rpi4',          '{"tier":"low","watt_capacity":15}',    now(), 1),
  ('nexus-pico','pico-w',        '{"tier":"embedded","watt_capacity":1}', now(), 1);

INSERT OR IGNORE INTO arena_edges VALUES
  ('e1', 'nexus-m4',  'nexus-rpi',  'energy-link', '{"latency_ms":2}',   1.0),
  ('e2', 'nexus-rpi', 'nexus-pico', 'energy-link', '{"latency_ms":50}',  0.5),
  ('e3', 'nexus-pico','nexus-m4',   'energy-link', '{"latency_ms":45}',  0.3);

-- Query: neighbor energy capacity
SELECT n.id, n.label, n.properties->>'watt_capacity' AS watts,
       COUNT(e.id) AS degree
FROM arena_nodes n
LEFT JOIN arena_edges e ON n.id = e.src OR n.id = e.dst
GROUP BY n.id, n.label, watts;
```

### Nashator Transactive Energy API

Submit energy bids and query equilibrium via the Nashator service:

```bash
# Check Nashator is running
curl -s http://127.0.0.1:9999/health

# Submit an energy bid (open game move)
curl -X POST http://127.0.0.1:9999/api/v1/bid \
  -H 'Content-Type: application/json' \
  -d '{
    "node_id": "nexus-m4",
    "bid_type": "supply",
    "quantity_kwh": 5.0,
    "price_per_kwh": 0.12,
    "timestamp": "'"$(date -u +%Y-%m-%dT%H:%M:%SZ)"'"
  }'

# Query current correlated equilibrium (market clearing price)
curl -s http://127.0.0.1:9999/api/v1/equilibrium | python3 -m json.tool
```

### Open Games Grid Model (Julia)

Compose a transactive energy game using Open Games:

```julia
# Requires: using Pkg; Pkg.add(["OpenGames", "Catlab"])
using OpenGames, Catlab

# Each Nexus Node is a player choosing (quantity, price)
node_game = OpenGame(
    name = :nexus_node,
    strategies = [(0.0:0.5:10.0, 0.05:0.01:0.30)],  # (kWh, $/kWh)
    payoff = (s, ctx) -> s[2] * s[1] - generation_cost(s[1])
)

# Transmission: pairwise latency cost
transmission_game = OpenGame(
    name = :transmission,
    payoff = (s, ctx) -> -ctx[:latency_ms] * 0.001 * s[:quantity]
)

# Compose: node @ transmission @ market
grid_game = compose(node_game, transmission_game)

# Find Nash equilibrium via Lemke-Howson or support enumeration
eq = solve(grid_game, method=:support_enumeration)
println("Equilibrium price: ", eq.clearing_price, " \$/kWh")
```

### Gromov-Wasserstein Network Matching (Python)

Compare two energy network topologies using entropic GW distance:

```python
# pip install pot numpy
import numpy as np
import ot

# Adjacency / cost matrices for two energy networks
C1 = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]], dtype=float)  # linear
C2 = np.array([[0, 1, 1], [1, 0, 1], [1, 1, 0]], dtype=float)  # triangle

p = ot.unif(C1.shape[0])
q = ot.unif(C2.shape[0])

# Entropic Gromov-Wasserstein distance
gw_dist, log = ot.gromov.entropic_gromov_wasserstein2(
    C1, C2, p, q, loss_fun='square_loss', epsilon=0.1, log=True
)
print(f"Entropic GW distance: {gw_dist:.6f}")
print(f"Transport plan:\n{log['T']}")
```

## Gap Registry

| Ontology Concept | Gap | Priority | Candidate Skill |
|---|---|---|---|
| Gromov-Wasserstein distance | No dedicated GW/OT skill | HIGH | `gromov-wasserstein` |
| Arena graph store (Rust+Yrs) | No Rust CRDT skill | MED | `arena-crdt` |
| Stigmergic feedback loops | No stigmergy skill | MED | `stigmergy` |
| WasmEdge runtime | hvm-runtime covers HVM, not WasmEdge | LOW | `wasmedge-runtime` |

## Plurigrid Protocol Summary

- **Math core**: Open Games + Gromov-Wasserstein + Active Inference
- **Data layer**: Arena (local-first CRDT graph DB, Rust + Yrs + DuckDB)
- **Agent arch**: Digital twins with value elicitation + mutual recursion
- **Equilibrium**: Autopoietically ergodic state = Nash eq. that is thermodynamically stable
- **Energy market**: Stigmergic feedback -> decentralized price discovery
- **Hardware**: Nexus Nodes (Apple Silicon / RPi4 / Pico W) all running WASI
