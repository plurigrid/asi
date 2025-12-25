# Monad & Comonad Color Types Catalog

> Every monad and comonad in the ASI ecosystem, classified by GF(3) trit and deterministic color.

---

## Color Assignment Formula

```julia
# SplitMix64 deterministic color from type name
function monad_color(type_name::String, seed::UInt64 = 0x42D)
    hash = splitmix64(seed ⊻ hash(type_name))
    hue = (hash % 360)
    LCH(55, 70, hue)
end
```

---

## Complete Type Registry

### PLUS (+1) Monads — Generators (Red Spectrum)

| Type | Trit | Hex Color | Role | Dual |
|------|------|-----------|------|------|
| **Free f** | +1 | `#D82626` | Syntactic tree generation | Cofree |
| **Writer w** | +1 | `#E63946` | Log/output accumulation | Traced |
| **IO** | +1 | `#FF4136` | World-state transformation | — |
| **List** | +1* | `#DC143C` | Nondeterministic generation | — |
| **ColorFree** | +1 | `#D82626` | Gay.jl color stream syntax | ColorCofree |
| **FreeMonad** | +1 | `#D82626` | Python free monad impl | Cofree |
| **Producer** | +1 | `#FF6B6B` | Conduit/pipe generation | Consumer |
| **Gen** | +1 | `#E74C3C` | QuickCheck generation | — |
| **Emit** | +1 | `#C0392B` | Event emission | — |

*List trit = `length mod 3`; default +1 for non-empty

### ERGODIC (0) Monads — Transporters (Green Spectrum)

| Type | Trit | Hex Color | Role | Dual |
|------|------|-----------|------|------|
| **Just/Identity** | 0 | `#26D826` | Pure value wrapper | Identity |
| **Reader r** | 0 | `#2ECC71` | Environment access | Env |
| **Cont r** | 0 | `#27AE60` | Control flow/CPS | — |
| **ST s** | 0 | `#1ABC9C` | Scoped mutation | — |
| **RWS r w s** | 0 | `#16A085` | Combined reader/writer/state | — |
| **Validation** | 0 | `#00B894` | Accumulating errors | — |
| **Parser** | 0 | `#55EFC4` | Context-free parsing | — |
| **Gay** | 0 | `#26D826` | Deterministic color RNG | — |
| **Kan** | 0 | `#00CEC9` | Kan extension transport | — |

### MINUS (-1) Monads — Validators/Terminators (Blue Spectrum)

| Type | Trit | Hex Color | Role | Dual |
|------|------|-----------|------|------|
| **Maybe (Nothing)** | -1 | `#2626D8` | Failure/absence | — |
| **Either (Left)** | -1 | `#3498DB` | Error case | — |
| **Except e** | -1 | `#2980B9` | Exception handling | — |
| **State (get)** | -1 | `#5DADE2` | State extraction | put (+1) |
| **Select** | -1 | `#1E90FF` | Selection/focusing | — |
| **Logic** | -1 | `#0984E3` | Backtracking search | — |

---

## Complete Comonad Registry

### MINUS (-1) Comonads — Observers (Blue Spectrum)

| Type | Trit | Hex Color | Role | Dual |
|------|------|-----------|------|------|
| **Cofree f** | -1 | `#2626D8` | Semantic observation stream | Free |
| **Store s** | -1 | `#3742FA` | Position-focused context | — |
| **Env e** | -1 | `#5352ED` | Tagged environment context | Reader |
| **Traced m** | -1 | `#686DE0` | Accumulated history | Writer |
| **Stream** | -1 | `#7B68EE` | Infinite observation | — |
| **NonEmpty** | -1 | `#6C5CE7` | Non-empty observation | — |
| **Coreader** | -1 | `#A29BFE` | Dual to reader | — |
| **ColorCofree** | -1 | `#2626D8` | Gay.jl color observation | ColorFree |

### ERGODIC (0) Comonads — Neutral (Green Spectrum)

| Type | Trit | Hex Color | Role | Dual |
|------|------|-----------|------|------|
| **Identity** | 0 | `#26D826` | Trivial comonad | Identity |
| **Coproduct** | 0 | `#00B894` | Sum comonad | Product |

---

## Monad Transformers (Composite Trits)

| Transformer | Base Trit | Stack Rule | Example |
|-------------|-----------|------------|---------|
| **ReaderT r m** | 0 | `trit(m)` | ReaderT r IO = +1 |
| **WriterT w m** | +1 | `(+1 + trit(m)) mod 3` | WriterT w Maybe = 0 |
| **StateT s m** | ±1 | `(op_trit + trit(m)) mod 3` | StateT s (get) Reader = -1 |
| **ExceptT e m** | -1 | `(-1 + trit(m)) mod 3` | ExceptT e IO = 0 |
| **ContT r m** | 0 | `trit(m)` | ContT r Writer = +1 |
| **FreeT f m** | +1 | `(+1 + trit(m)) mod 3` | FreeT f Cofree = 0 ✓ |
| **CofreeT f w** | -1 | `(-1 + trit(w)) mod 3` | CofreeT f Free = 0 ✓ |

### Transformer Stack Conservation

```haskell
-- Valid transformer stacks sum to 0 (mod 3)
ReaderT r (WriterT w (ExceptT e IO))
  = 0 + (+1 + (-1 + +1)) 
  = 0 + 1 = +1

-- Add one more layer to balance:
ExceptT e' (ReaderT r (WriterT w (ExceptT e IO)))
  = -1 + 1 = 0 ✓
```

---

## MCP Server Types (from mcp_usage_tracker.rb)

### MINUS (-1) Servers — Validators

| Server | Trit | Color | Latency | Local |
|--------|------|-------|---------|-------|
| `tree-sitter` | -1 | `#2626D8` | 50ms | ✓ |
| `radare2` | -1 | `#3498DB` | 200ms | ✓ |
| `sheaf-cohomology` | -1 | `#2626D8` | 20ms | ✓ |
| `temporal-coalgebra` | -1 | `#2980B9` | 15ms | ✓ |
| `persistent-homology` | -1 | `#5DADE2` | 100ms | ✓ |

### ERGODIC (0) Servers — Transporters

| Server | Trit | Color | Latency | Local |
|--------|------|-------|---------|-------|
| `gay` | 0 | `#26D826` | 10ms | ✓ |
| `huggingface` | 0 | `#2ECC71` | 500ms | ✗ |
| `babashka` | 0 | `#27AE60` | 100ms | ✓ |
| `unison` | 0 | `#1ABC9C` | 300ms | ✓ |
| `kan-extensions` | 0 | `#00CEC9` | 25ms | ✓ |
| `dialectica` | 0 | `#16A085` | 20ms | ✓ |
| `open-games` | 0 | `#55EFC4` | 30ms | ✓ |

### PLUS (+1) Servers — Generators

| Server | Trit | Color | Latency | Local |
|--------|------|-------|---------|-------|
| `firecrawl` | +1 | `#D82626` | 2000ms | ✗ |
| `exa` | +1 | `#E63946` | 1000ms | ✗ |
| `marginalia` | +1 | `#FF4136` | 500ms | ✗ |
| `free-monad-gen` | +1 | `#D82626` | 35ms | ✓ |
| `operad-compose` | +1 | `#E74C3C` | 25ms | ✓ |
| `topos-generate` | +1 | `#DC143C` | 50ms | ✓ |

---

## Rust/Bafishka Categorical Properties

From `genesis_seeds.rs`:

```rust
struct CategoricalProperties {
    monad_strength: f64,      // positive_trits / count → higher = more generative
    functor_preservation: f64, // 1.0 - negative_trits * 0.3
    comonad_duality: f64,     // zero_trits * 0.8 + 0.2 → higher = more ergodic
    simd_alignment: bool,     // trit_count % 4 == 0
    arena_allocation: bool,   // positive_trits > negative_trits
    stigmergic_amplification: f64, // |trit_sum| / count * 2.0 + 0.5
}
```

### Trit-to-Property Mapping

| Property | +1 Trits | 0 Trits | -1 Trits |
|----------|----------|---------|----------|
| `monad_strength` | ↑ High | — | ↓ Low |
| `comonad_duality` | ↓ Low | ↑ High | — |
| `arena_allocation` | ✓ Enable | — | ✗ Disable |

---

## Open Games Engine StateT Usage

From `open-game-engine/src/OpenGames/Engine/*.hs`:

```haskell
-- StochasticStatefulContext: Games with probabilistic state
data StochasticStatefulContext s t a b where
  StochasticStatefulContext 
    :: Stochastic (z, s) 
    -> (z -> a -> StateT Vector Stochastic b) 
    -> StochasticStatefulContext s t a b

-- MonadContext: IO-based games
data MonadContext s t a b where
  MonadContext 
    :: IO (z, s) 
    -> (z -> a -> StateT Vector IO b) 
    -> MonadContext s t a b
```

### Open Games Color Assignment

| Game Type | Monad Stack | Trit |
|-----------|-------------|------|
| `StochasticStatefulOptic` | `StateT Vector Stochastic` | 0 (ergodic) |
| `MonadOptic` | `StateT Vector IO` | +1 (generative) |
| `extractContinuation` | `StateT Vector m ()` | -1 (observation) |

---

## Gay.jl Thread Findings Monad

From `Gay.jl/src/thread_findings.jl`:

```julia
# ReaderT ThreadContext (Writer FindingsSet)
# Combined trit: 0 + 1 = 1 (mod 3)

struct VerificationMonad{A}
    run::Function  # ThreadContext → (A, FindingsSet)
    trit::Int      # +1 (generative discovery)
end
```

---

## Skill Bundle Color Types

### Cohomological Bundle (Sum = 0)

```
sheaf-cohomology    (-1) #2626D8  ─┐
kan-extensions      ( 0) #26D826   ├─ Σ = 0 ✓
free-monad-gen      (+1) #D82626  ─┘
```

### Game Bundle (Sum = 0)

```
temporal-coalgebra  (-1) #2626D8  ─┐
dialectica          ( 0) #26D826   ├─ Σ = 0 ✓
operad-compose      (+1) #D82626  ─┘
```

### Topos Bundle (Sum = 0)

```
persistent-homology (-1) #2626D8  ─┐
open-games          ( 0) #26D826   ├─ Σ = 0 ✓
topos-generate      (+1) #D82626  ─┘
```

---

## Visual Color Wheel

```
                    +1 PLUS (Red)
                    #D82626
                       ▲
                      / \
                     /   \
                    /     \
                   /       \
      0 ERGODIC ◄─────────────► -1 MINUS
      (Green)                   (Blue)
      #26D826                   #2626D8
```

---

## Implementation: Color Type Lookup

```python
# Python lookup table
MONAD_COLORS = {
    # PLUS (+1)
    "Free": {"trit": 1, "hex": "#D82626", "hue": 0},
    "Writer": {"trit": 1, "hex": "#E63946", "hue": 5},
    "IO": {"trit": 1, "hex": "#FF4136", "hue": 10},
    "ColorFree": {"trit": 1, "hex": "#D82626", "hue": 0},
    
    # ERGODIC (0)
    "Just": {"trit": 0, "hex": "#26D826", "hue": 120},
    "Reader": {"trit": 0, "hex": "#2ECC71", "hue": 130},
    "Cont": {"trit": 0, "hex": "#27AE60", "hue": 140},
    "Gay": {"trit": 0, "hex": "#26D826", "hue": 120},
    
    # MINUS (-1)
    "Maybe": {"trit": -1, "hex": "#2626D8", "hue": 240},
    "Cofree": {"trit": -1, "hex": "#2626D8", "hue": 240},
    "Store": {"trit": -1, "hex": "#3742FA", "hue": 235},
    "Traced": {"trit": -1, "hex": "#686DE0", "hue": 250},
}

def get_monad_color(type_name: str) -> dict:
    return MONAD_COLORS.get(type_name, {"trit": 0, "hex": "#26D826", "hue": 120})
```

```julia
# Julia lookup
const MONAD_COLORS = Dict(
    # PLUS (+1)
    :Free => (trit=1, hex="#D82626", hue=0),
    :Writer => (trit=1, hex="#E63946", hue=5),
    :IO => (trit=1, hex="#FF4136", hue=10),
    
    # ERGODIC (0)
    :Just => (trit=0, hex="#26D826", hue=120),
    :Reader => (trit=0, hex="#2ECC71", hue=130),
    :Cont => (trit=0, hex="#27AE60", hue=140),
    
    # MINUS (-1)
    :Maybe => (trit=-1, hex="#2626D8", hue=240),
    :Cofree => (trit=-1, hex="#2626D8", hue=240),
    :Store => (trit=-1, hex="#3742FA", hue=235),
)

monad_color(t::Symbol) = get(MONAD_COLORS, t, (trit=0, hex="#26D826", hue=120))
```

---

## Summary Statistics

| Category | Count | Primary Hue Range |
|----------|-------|-------------------|
| PLUS (+1) Monads | 9 | 0°–30° (Red) |
| ERGODIC (0) Monads | 9 | 120°–180° (Green) |
| MINUS (-1) Monads | 6 | 200°–250° (Blue) |
| MINUS (-1) Comonads | 8 | 235°–280° (Blue-Violet) |
| ERGODIC (0) Comonads | 2 | 120°–150° (Green) |
| **Total** | **34** | Full spectrum |

---

## References

- [free_cofree_monad_composition.py](file:///Users/bob/ies/free_cofree_monad_composition.py)
- [music-topos/lib/mcp_usage_tracker.rb](file:///Users/bob/ies/music-topos/lib/mcp_usage_tracker.rb)
- [hatchery_repos/bmorphism__bafishka/.../genesis_seeds.rs](file:///Users/bob/ies/hatchery_repos/bmorphism__bafishka/bafishka/bafishka/src/genesis_seeds.rs)
- [plurigrid-asi-skillz/skills/free-monad-gen/SKILL.md](file:///Users/bob/ies/plurigrid-asi-skillz/skills/free-monad-gen/SKILL.md)
- [Gay.jl/src/thread_findings.jl](file:///Users/bob/ies/Gay.jl/src/thread_findings.jl)
