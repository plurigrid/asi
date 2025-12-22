# Neural Wiring Diagrams × music-topos

## Source
[Topos Institute Blog: Neural Wiring Diagrams](https://topos.institute/blog/2024-11-08-neural-wiring-diagrams/)
- **Authors**: David Spivak, Sophie Libkind
- **Date**: November 8, 2024

## Key Concepts

### Recumbent Wiring Diagrams (rWD)
Operadic structures for message-passing protocols with the constraint:
> "No two vertices/boxes occur at the same time"

This **sequential constraint** distinguishes them from general string diagrams.

### Neural Wiring Diagrams (nWD)
Relaxations allowing:
- **Wire splitting**: One wire → multiple boxes (Frobenius!)
- **Feedback loops**: Circular information flow
- **Polynomial representations**: Boxes as polynomials

### The Functor
```
MP: rnWD → ℙrg_𝔪
```
Maps message-passing diagrams into the full agent operad.

---

## Connection to music-topos

### 1. DisCoPy String Diagrams ↔ Wiring Diagrams

| DisCoPy (our impl) | Neural Wiring Diagrams |
|--------------------|------------------------|
| `Box("C4", Note, Note)` | Vertex with ports |
| `>>` composition | Sequential constraint |
| `@` tensor | Parallel wires |
| `Spider(1, n, Ty)` | Wire splitting |
| Frobenius algebra | Feedback loops |

### 2. Parallel Sexp Execution ↔ Task Delegation

Our `ParallelSexpExecutor` in `discohy.hy`:
```hy
(defclass ParallelSexpExecutor []
  (defn execute-parallel [self sexps handler]
    (with [executor (ThreadPoolExecutor)]
      ;; Task delegation pattern
      (for [sexp sexps]
        (.submit executor self.execute-one sexp handler)))))
```

Maps to Spivak's "evolving planners" - agents maintaining internal state while delegating work.

### 3. Simultaneity Surfaces ↔ Polynomial Functors

Our 3-stream architecture:
```
LIVE (+1)     ─────────────────→  Forward colors
VERIFY (0)    ─────────────────→  Self-verification
BACKFILL (-1) ─────────────────→  Historical colors
```

Corresponds to polynomial functor structure:
```
Box: InputSets → Outcomes
Stream: Seed × Index → Color
```

### 4. Time Travel ↔ Feedback Loops

DuckDB time travel in `gay_world_ducklake.hy`:
```hy
(defn time-travel [self target-index stream-name]
  ;; Feedback: future state depends on past
  (setv pattern [stream.index target-index stream.tap-state])
  (when (in pattern self.disallowed-patterns)
    ;; Möbius inversion prevents paradoxes
    (return {"error" "Time travel pattern disallowed"})))
```

---

## The Simultaneity Triangle (Extended)

```
                    Topos Institute
                   (Spivak/Libkind)
                   Neural Wiring Diagrams
                         │
                         ↓
            ┌────────────┴────────────┐
            │                         │
       DisCoPy                   AlgebraicJulia
    (toumix/QNLP)              (ACSets/Catlab)
            │                         │
            └──────────┬──────────────┘
                       │
                       ↓
                  music-topos
              (Gay.jl seed 1069)
                       │
                       ↓
               Rubato Composer
                  (Mazzola)
```

---

## Key People Network

| Person | Affiliation | Contribution |
|--------|-------------|--------------|
| David Spivak | Topos Institute | Polynomial functors, operads |
| Sophie Libkind | Topos/AlgebraicJulia | StructuredDecompositions.jl |
| Alexis Toumi | DisCoPy | String diagrams for QNLP |
| Bruno Gavranović | CT+ML | Categorical deep learning |
| Guerino Mazzola | Rubato | Topos of Music |

---

## Implementation Bridge

### From Neural Wiring to Sound

```python
# lib/discopy_bridge.py pattern
from discopy.frobenius import Spider, Ty

# Wire splitting = Voice leading
FrobNote = Ty("Note")
split = Spider(1, 3, FrobNote)  # 1 voice → 3 voices

# This IS neural wiring!
# Box with 1 input port, 3 output ports
# Compositional message passing
```

### From Polynomial to Color Stream

```hy
;; lib/gay_world_ducklake.hy pattern
(defn color-at [seed index]
  ;; Polynomial functor: Seed × Index → Color
  (setv state seed)
  (for [_ (range index)]
    (setv [state _] (splitmix64 state)))
  {"L" L "C" C "H" H "index" index "seed" seed})
```

---

## Future Directions

1. **Implement rnWD operad** in AlgebraicJulia
2. **Map DisCoPy diagrams** to polynomial functors
3. **Audio feedback loops** via neural wiring semantics
4. **Multi-agent music** with task delegation patterns

---

## See Also

- `SIMULTANEITY_SURFACE.md` - The convergence discovery
- `lib/discopy_bridge.py` - DisCoPy string diagrams
- `lib/discohy.hy` - Parallel sexp execution
- `lib/gay_world_ducklake.hy` - Time travel surfaces
