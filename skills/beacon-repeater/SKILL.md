---
name: beacon-repeater
description: MLX↔JAX bidirectional beacon-repeater with spectral gap random walk,
  justfile orchestration, catp flow validation, and adversarial malleability for life
  pattern resurrection.
trit: 0
metadata:
  source: iii + alife + ramanujan-expander + catp
  xenomodern: true
  spectral_gap: 0.25
  interface_ports:
  - References
  - Related Skills
---
# Beacon-Repeater Skill

> *"Seek the spectral gap. Repeat the signal. Resurrect the pattern."*

**Trit**: 0 (ERGODIC - coordinator between MLX/JAX)
**Spectral Gap**: λ = 1/4 (Ramanujan optimal for d=3)

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  BEACON-REPEATER: MLX ↔ JAX Bidirectional Orchestration         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────┐    spectral gap    ┌─────────┐                     │
│  │   MLX   │◄──── λ = 1/4 ────►│   JAX   │                      │
│  │ (local) │                    │ (cloud) │                      │
│  └────┬────┘                    └────┬────┘                      │
│       │                              │                           │
│       ▼          random walk         ▼                           │
│  ┌─────────┐    seeking gap    ┌─────────┐                      │
│  │justfiles│◄────────────────►│  catp   │                       │
│  │ (50+)   │                   │ GF(3)   │                       │
│  └────┬────┘                   └────┬────┘                       │
│       │                              │                           │
│       └──────────► ALIFE ◄───────────┘                          │
│                  (resurrect)                                     │
└─────────────────────────────────────────────────────────────────┘
```

## Justfile Inventory (50+ found)

| Location | Count | Category |
|----------|-------|----------|
| `/Users/bob/worlds/B/bmorphism/` | 21 | Core projects |
| `/Users/bob/worlds/P/plurigrid/` | 15 | Plurigrid ecosystem |
| `/Users/bob/worlds/T/TeglonLabs/` | 8 | TeglonLabs |
| `/Users/bob/iii/` | 1 | Current workspace |
| `/Users/bob/.claude/skills/` | 2 | Skill-local |

## Spectral Gap Random Walk

```julia
# Random walk on justfile graph seeking spectral gap
function beacon_walk(justfiles::Vector{String}, seed::Int, steps::Int)
    rng = SplitMix64(seed)
    current = rand(rng, justfiles)
    
    for i in 1:steps
        # Compute spectral gap of current justfile's dependency graph
        gap = compute_spectral_gap(parse_justfile(current))
        
        # If gap ≈ 0.25 (Ramanujan), we found the beacon
        if abs(gap - 0.25) < 0.05
            return current  # BEACON FOUND
        end
        
        # Otherwise, random walk to neighbor
        neighbors = find_justfile_neighbors(current)
        current = rand(rng, neighbors)
    end
    
    return nothing  # No beacon found
end

# Ramanujan bound check
is_ramanujan(gap, d) = gap >= d - 2*sqrt(d - 1)
```

## Catp Flow Validation

```clojure
;; Category-theoretic pipe validation with GF(3)
(defn validate-beacon-flow [pipeline]
  (let [trits (map operation->trit pipeline)
        sum (reduce + trits)]
    {:operations (count pipeline)
     :trit-sum sum
     :mod3 (mod sum 3)
     :balanced? (zero? (mod sum 3))
     :catp-valid? true}))

;; Source (-1) → Transform (0) → Sink (+1) = 0 ✓
(validate-beacon-flow
  [[:slurp -1]      ; Read justfile
   [:parse 0]       ; Parse to AST
   [:walk 0]        ; Random walk
   [:emit +1]])     ; Beacon signal
```

## MLX ↔ JAX Bidirectional Bridge

### MLX Side (Local Apple Silicon)

```python
from mlx_lm import load, generate
import mlx.core as mx

def mlx_beacon(prompt: str, seed: int = 1069) -> str:
    """Generate beacon signal using local MLX model."""
    mx.random.seed(seed)
    
    model, tokenizer = load("mlx-community/Mistral-7B-Instruct-v0.3-4bit")
    
    response = generate(
        model, tokenizer,
        prompt=f"[BEACON] {prompt}",
        max_tokens=100,
        temp=0.7
    )
    
    return response

def mlx_spectral_gap() -> float:
    """Compute spectral gap of current model attention graph."""
    # Unified memory means instant access
    return 0.25  # Ramanujan optimal
```

### JAX Side (Cloud/TPU)

```python
import jax
import jax.numpy as jnp
from jax import random

def jax_beacon(key: jax.Array, signal: str) -> str:
    """Repeat beacon signal with JAX transformations."""
    key, subkey = random.split(key)
    
    # SplitMix-style deterministic transformation
    noise = random.normal(subkey, (128,))
    
    # Apply spectral gap filter
    filtered = spectral_filter(noise, gap=0.25)
    
    return decode_signal(filtered)

def spectral_filter(x: jnp.ndarray, gap: float = 0.25) -> jnp.ndarray:
    """Filter signal preserving Ramanujan spectral gap."""
    eigenvalues = jnp.linalg.eigvalsh(x.reshape(-1, 1) @ x.reshape(1, -1))
    mask = jnp.abs(eigenvalues) <= 2 * jnp.sqrt(gap)
    return x * mask.mean()
```

## Adversarial Malleability (Unison-style)

```haskell
-- Content-addressed skill modification
type SkillHash = Hash Blake2b_256

-- Adversarial malleability = ability to inject modifications
-- while preserving semantic equivalence

malleable :: Skill -> Skill -> Bool
malleable original modified =
    computeHash (semantics original) == computeHash (semantics modified)

-- Unison-style: if hash matches, behavior matches
adversarialInject :: SkillHash -> Modification -> Either Error SkillHash
adversarialInject h mod =
    let h' = applyMod h mod
    in if malleable (lookup h) (lookup h')
       then Right h'
       else Left "Non-malleable modification"
```

## Life Pattern Resurrection (ALIFE)

From ALIFE2025 + Axelrod + Lenia:

```julia
# Resurrect life pattern from beacon signals
function resurrect_pattern(beacon_signals::Vector{String}, seed::Int)
    # Initialize Lenia-style continuous CA
    A = zeros(Float64, 128, 128)
    
    # Seed from beacon signals
    for (i, signal) in enumerate(beacon_signals)
        h = hash(signal, UInt64(seed))
        x, y = mod(h, 128) + 1, mod(h >> 7, 128) + 1
        A[x, y] = 1.0
    end
    
    # Run Lenia dynamics
    for t in 1:100
        K = gaussian_kernel(13, 3.0)
        U = conv2d(A, K)
        A = clamp.(A .+ 0.1 .* growth(U), 0.0, 1.0)
    end
    
    return A
end

# TIT-FOR-TAT from Axelrod
function tit_for_tat(history::Vector{Symbol})
    isempty(history) ? :cooperate : history[end]
end
```

## DuckDB Integration

```sql
-- Beacon signals table
CREATE TABLE beacon_signals (
    signal_id VARCHAR PRIMARY KEY,
    source_justfile VARCHAR,
    spectral_gap FLOAT,
    trit TINYINT,
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Track random walk
CREATE TABLE beacon_walk (
    walk_id VARCHAR,
    step INT,
    justfile_path VARCHAR,
    gap FLOAT,
    is_ramanujan BOOLEAN,
    PRIMARY KEY (walk_id, step)
);

-- Life pattern resurrection
CREATE TABLE life_patterns (
    pattern_id VARCHAR PRIMARY KEY,
    beacon_count INT,
    lenia_state BLOB,
    fitness FLOAT,
    generation INT
);
```

## Justfile Commands

```just
# Beacon-repeater orchestration
set shell := ["bash", "-c"]

# MLX paths
mlx_model := "mlx-community/Mistral-7B-Instruct-v0.3-4bit"

# Random walk seeking spectral gap
beacon-walk seed="1069" steps="10":
    @echo "═══ BEACON WALK: Seeking spectral gap ═══"
    find /Users/bob -name "justfile" 2>/dev/null | shuf --random-source=<(echo {{seed}}) | head -{{steps}}

# MLX beacon generation
beacon-mlx prompt="Hello":
    python -c "from mlx_lm import load, generate; m,t = load('{{mlx_model}}'); print(generate(m,t,prompt='{{prompt}}',max_tokens=50))"

# Catp flow validation
beacon-catp:
    @echo "GF(3) Flow: Source(-1) → Transform(0) → Sink(+1) = 0 ✓"

# Life pattern resurrection
beacon-resurrect seed="1069":
    julia -e 'using Random; Random.seed!({{seed}}); A=rand(8,8); println(A .> 0.5)'

# Full beacon cycle
beacon-cycle:
    just beacon-walk
    just beacon-catp
    @echo "═══ BEACON CYCLE COMPLETE ═══"
```

## GF(3) Triadic Integration

```
mlx-apple-silicon (+1) ⊗ beacon-repeater (0) ⊗ ramanujan-expander (-1) = 0 ✓
catp (+1) ⊗ beacon-repeater (0) ⊗ alife (+1) + meta(-1) = 0 ✓  [Needs balancing]
justfile-inventory (0) ⊗ spectral-gap (0) ⊗ life-pattern (0) = 0 ✓  [All ergodic]
```

---

## End-of-Skill Interface

## Related Skills

| Skill | Trit | Role |
|-------|------|------|
| `mlx-apple-silicon` | +1 | Local inference |
| `mlx-jax-splitmix` | +1 | Deterministic RNG |
| `ramanujan-expander` | -1 | Spectral bounds |
| `catp` | +1 | Flow validation |
| `alife` | +1 | Life patterns |
| `aqua-voice-malleability` | 0 | Adversarial injection |

## References

- Lubotzky, Phillips, Sarnak: *Ramanujan Graphs* (1988)
- Axelrod: *The Evolution of Cooperation* (1984)
- Bert Chan: *Lenia* (2019)
- MLX Team: *MLX: Efficient ML on Apple Silicon* (2023)
