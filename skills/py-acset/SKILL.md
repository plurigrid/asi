# py-acset Skill

> **Trit**: 0 (ERGODIC - Coordinator)
> Self-improving Python ACSets with Ollama action space integration.
> Evolves on each interaction via compression progress tracking.

## Overview

Python-native Attributed C-Sets with:
- **Streaming Ollama integration** for LLM action spaces
- **ThreadPoolExecutor parallelism** (configurable num_parallel)
- **GF(3) load balancing** across request fanout
- **Self-improvement loop** via interaction logging

## GF(3) Triad

```
acsets-hatchery (-1) ⊗ py-acset (0) ⊗ gay-mcp (+1) = 0 ✓
```

## Quick Start

```bash
# Run with flox ollama environment
flox activate -r flox/ollama -s
uv run python -m py_acset

# Or directly
uv run --with httpx python src/py_acset/main.py
```

## Schema Definition (S-expression style)

```python
OLLAMA_SCHEMA = {
    'objects': {'Model', 'Request', 'Response', 'Runner', 'GPU'},
    'morphisms': {
        'request_model': ('Request', 'Model'),
        'response_request': ('Response', 'Request'),
        'runner_model': ('Runner', 'Model'),
        'runner_gpu': ('Runner', 'GPU'),
    },
    'attributes': {
        'Model': {'name': str, 'size': int, 'parameters': int},
        'Request': {'id': str, 'type': str, 'prompt': str, 'status': str, 'trit': int},
        'Response': {'chunk': str, 'done': bool, 'sequence': int},
        'Runner': {'num_parallel': int, 'active': int},
        'GPU': {'memory_total': int, 'memory_free': int},
    }
}
```

## API Endpoints Mapped

| Endpoint | Streaming | ACSet Object | Parallelism |
|----------|-----------|--------------|-------------|
| `/api/generate` | ✅ | Request→Response | semaphore(n) |
| `/api/chat` | ✅ | Request→Response | semaphore(n) |
| `/api/embed` | ❌ batch | Request→Response | thread pool |
| `/api/pull` | ✅ progress | — | single |
| `/api/tags` | ❌ | Model | — |
| `/api/ps` | ❌ | Runner | — |

## Core Classes

### ACSet

```python
from py_acset import ACSet, OLLAMA_SCHEMA

acset = ACSet(OLLAMA_SCHEMA)

# Add model
model_id = acset.add_part('Model', name='llama3.2', size=2_000_000_000)

# Add request with GF(3) trit
req_id = acset.add_part('Request', 
    id='uuid-123',
    type='generate', 
    prompt='Hello',
    trit=1,  # PLUS: generator
    model_fk=model_id)

# Query
acset.parts('Request')
acset.nparts('Response')
```

### ParallelDispatcher

```python
from py_acset import OllamaConfig, ParallelDispatcher

config = OllamaConfig(
    base_url="http://localhost:11434",
    num_parallel=4,
    max_queue=512
)

dispatcher = ParallelDispatcher(config)

# Streaming generate
request_id, stream = dispatcher.action_generate(
    model="llama3.2",
    prompt="Explain ACSets",
    callback=lambda chunk: print(chunk.get('response', ''), end='')
)

# Collect when done
for chunk in stream:
    if chunk is None:
        break
```

### Parallel Fanout with GF(3)

```python
from py_acset import parallel_fanout, collect_streams

prompts = ["Query 1", "Query 2", "Query 3"]
streams, trits = parallel_fanout(dispatcher, "llama3.2", prompts, 
                                  trit_assignment="balanced")

# trits = [-1, 0, +1] for balanced
# trits = [+1, +1, +1] for "generator"

results = collect_streams(streams, timeout=60.0)
```

## Self-Improvement Loop

Each interaction logs to DuckDB for compression progress:

```python
from py_acset import log_interaction, get_improvement_delta

# Automatic logging
log_interaction(
    action="generate",
    model="llama3.2", 
    tokens_in=50,
    tokens_out=200,
    latency_ms=1500
)

# Check improvement
delta = get_improvement_delta()
# Returns: {'compression_ratio': 0.85, 'latency_improvement': 0.12, ...}
```

## Commands

```bash
# List models
just py-acset-models

# Generate (streaming)
just py-acset-generate "llama3.2" "What is category theory?"

# Parallel fanout
just py-acset-fanout "llama3.2" 3 "Explain X" "Compare Y" "Define Z"

# Self-improvement stats
just py-acset-stats
```

## File Structure

```
src/py_acset/
├── __init__.py          # Exports
├── acset.py             # ACSet core
├── schema.py            # OLLAMA_SCHEMA
├── dispatcher.py        # ParallelDispatcher
├── streaming.py         # StreamChannel
├── fanout.py            # GF(3) parallel fanout
├── improvement.py       # Self-improvement tracking
└── main.py              # CLI entry point
```

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `OLLAMA_HOST` | `localhost:11434` | Ollama server |
| `OLLAMA_NUM_PARALLEL` | `4` | Concurrent requests per model |
| `OLLAMA_MAX_QUEUE` | `512` | Max pending requests |
| `PY_ACSET_DB` | `~/.topos/py_acset.duckdb` | Improvement tracking |

## Dependencies

```toml
[project]
dependencies = [
    "httpx>=0.27",
    "duckdb>=1.0",
]
```

## Upstream: AlgebraicJulia/py-acsets

This skill wraps and extends the official [py-acsets](https://github.com/AlgebraicJulia/py-acsets) library:

```bash
pip install git+https://github.com/AlgebraicJulia/py-acsets.git
```

See [DISCREPANCIES.md](./DISCREPANCIES.md) for Julia↔Python API comparison.

### Key Gaps vs ACSets.jl

| Missing | Priority | Status |
|---------|----------|--------|
| `rem_part!` | P0 | 🔴 |
| `cascading_rem_part!` | P0 | 🔴 |
| Query DSL | P1 | 🔴 |
| `copy_parts!` | P1 | 🔴 |
| Name-based subpart lookup | P1 | 🟡 TODO |

## See Also

- `acsets-hatchery` - Julia ACSets reference
- `acsets-algebraic-databases` - Full ACSet theory
- `ollama-mcp` - MCP server for Ollama
- `gay-mcp` - Deterministic color generation
- `discohy-streams` - Categorical diagram streaming

## Traversal / Mixing Random Walks

```python
from py_acset import ACSetWalker, TriadicWalker, color_from_state

# Single walker
walker = ACSetWalker(acset, seed=1069)
for state in walker.walk(100, mode="lazy"):
    print(f"{state.ob}[{state.part_id}] trit={state.trit}")

# GF(3) triadic walkers (parallel)
triadic = TriadicWalker(acset, seed=1069)
results = triadic.mixing_race(target=50)
print(f"GF(3) conserved: {results['gf3_conserved']}")

# Deterministic color from state
color = color_from_state(state)  # e.g., "#e5a233"
```

### Walk Modes
| Mode | Description | Mixing |
|------|-------------|--------|
| `forward` | Follow hom direction only | Fast but may dead-end |
| `backward` | Incident queries only | Explores "causes" |
| `lazy` | Stay with prob 0.5 | Best mixing (Ramanujan) |
| `mixed` | Random forward/backward | Ergodic exploration |

### Spectral Gap
Default estimate: **1/4** (Ramanujan bound for regular graphs)

## Galois Connections & Cobordant Phase Space

### Subobject Classifier Ω

The 3-element Heyting algebra `{⊥, ?, ⊤}` ≅ GF(3) classifies subobjects:

```python
from py_acset import SubobjectClassifier

# Characteristic morphism χ: X → Ω
chi = SubobjectClassifier.chi(
    predicate=lambda x: x.trit == 1,      # In subobject?
    boundary=lambda x: x.trit == 0         # On boundary?
)

# χ(x) returns: -1 (⊥), 0 (?), +1 (⊤)
```

### Galois Connection: Color ⟷ Trit

```python
from py_acset import GaloisConnection, color_to_trit_galois

galois = color_to_trit_galois(seed=1069)

# Floor (left adjoint): Color → Trit (via hue thirds)
trit = galois.floor("#e5a233")  # → -1

# Ceiling (right adjoint): Trit → Color
color = galois.ceiling(-1)  # → "#e5e533"

# Adjunction property: ⌊q⌋ ≤ p ⟺ q ≤ ⌈p⌉
assert galois.verify_adjunction(trit, "#e5a233")
```

### Cobordant Phase Space (Pantleg)

Phase space with boundary = cobordism M: Σ_in → Σ_out

```python
from py_acset import CobordantPhaseSpace, Port, PortInterface

# Create cobordism with colored ports
cobord = CobordantPhaseSpace("Hamiltonian", dimension=2)

# Add pantleg boundaries (in = left leg, out = right leg)
cobord.add_pantleg_port("in", Port.from_seed("q", 1069, "in"))
cobord.add_pantleg_port("in", Port.from_seed("p", 1070, "in"))
cobord.add_pantleg_port("out", Port.from_seed("q'", 1069, "out"))

# Composition requires color matching on glued boundary
other = CobordantPhaseSpace("Evolution", dimension=2)
if cobord.can_compose_with(other):
    composed = cobord.compose(other)  # M ; N
```

### Colored Operads

Operations with colored inputs/outputs, GF(3) constraints:

```python
from py_acset import ColoredOperad, ColoredOperation

operad = ColoredOperad("OllamaOps", seed=1069)

operad.add_operation(ColoredOperation(
    name="generate",
    input_colors=["#e5a233"],   # prompt (trit=-1)
    output_color="#33e5a2",     # response (trit=0)
))

operad.add_operation(ColoredOperation(
    name="embed",
    input_colors=["#33e5a2", "#a233e5"],  # texts
    output_color="#e5a233",                # vector
))

# Compose if colors match
result = operad.compose("embed", 0, "generate")  # plug generate into slot 0

# Subobject classifier for balanced operations
chi = operad.subobject_classifier()
print(chi("generate"))  # χ = ? (boundary) or ⊤ (balanced)
```

### Port Graph Interface Pullback

```python
from py_acset import PortInterface, Port

# Two interfaces can compose if ports match
interface_A = PortInterface("source")
interface_A.add_port(Port.from_seed("data", 1069, "out"))

interface_B = PortInterface("sink")
interface_B.add_port(Port.from_seed("data", 1069, "in"))  # Same seed = same color

# Pullback composition
if interface_A.can_compose(interface_B):
    # Colors match, directions compatible (out↔in)
    print("Interfaces compose!")
```

## Categorical Structure Diagram

```
                    ColoredOperad
                         │
                    (operations)
                         ▼
    ┌─────────────────────────────────────┐
    │       Galois Connection             │
    │   ⌊⌋: Color → Trit (floor)          │
    │   ⌈⌉: Trit → Color (ceiling)        │
    └─────────────┬───────────────────────┘
                  │
         (lifts to subobjects)
                  ▼
    ┌─────────────────────────────────────┐
    │     SubobjectClassifier Ω           │
    │   χ: ACSet → {⊥, ?, ⊤}              │
    │   (characteristic morphism)          │
    └─────────────┬───────────────────────┘
                  │
         (classifies boundaries)
                  ▼
    ┌─────────────────────────────────────┐
    │   CobordantPhaseSpace               │
    │   ∂M = Σ_in ⊔ Σ_out                 │
    │   (pantleg = 2 boundaries)          │
    └─────────────┬───────────────────────┘
                  │
         (ports carry colors)
                  ▼
    ┌─────────────────────────────────────┐
    │      PortInterface                   │
    │   color matching via pullback        │
    │   GF(3) trit conservation           │
    └─────────────────────────────────────┘
```

## Handoff Fidelity Boundary

Models thread transitions as cobordism compositions:

```python
from py_acset import instantiate_current_handoff, Fidelity

# Instantiate boundary for current thread transition
boundary = instantiate_current_handoff()
report = boundary.fidelity_report()

# Classification: ⊤ (preserved), ? (at-risk), ⊥ (lost)
print(report['fidelity'])
# {'interior (⊤)': ['code', 'skills', 'duckdb'],
#  'boundary (?)': ['insights', 'state'],
#  'exterior (⊥)': ['rng', 'ephemeral']}

# Check composition viability
print(f"Can compose: {report['can_compose']}")
print(f"Matched ports: {report['matched_ports']}")

# Convert to explicit cobordism
cobord = boundary.to_cobordism()
```

### Fidelity Categories

| Category | Fidelity | Description |
|----------|----------|-------------|
| `code` | ⊤ Interior | Source files persist |
| `skill` | ⊤ Interior | Loaded skills persist |
| `duckdb` | ⊤ Interior | Databases persist |
| `insight` | ? Boundary | Derived understanding, may degrade |
| `state` | ? Boundary | In-memory state, needs verification |
| `ephemeral` | ⊥ Exterior | RNG state, streams - lost |

### Gluing via Color Matching

```
Σ_prev_out ≅ Σ_next_in  ⟺  ∀p: trit(p_prev) = trit(p_next)
```

Ports with matching colors (derived from same seed) compose. The Galois connection lifts color equality to categorical composition.

## Improvement History

| Date | Version | Delta | Notes |
|------|---------|-------|-------|
| 2026-01-07 | 0.1.0 | — | Initial schema + dispatcher |
| 2026-01-07 | 0.2.0 | +1 | Cloned upstream, discrepancy analysis |
| 2026-01-07 | 0.3.0 | +1 | Mixing random walk traversal |
| 2026-01-07 | 0.4.0 | +1 | Galois connections, subobject classifier, cobordant phase space |
| 2026-01-07 | 0.4.0 | +1 | Handoff fidelity boundary for thread transitions |

---

*Self-improving on each interaction. GF(3) conserved.*
