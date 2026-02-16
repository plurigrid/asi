---
name: polynomial-social-cognition
description: Social cognition via polynomial functors - "Agent" IS a polynomial p(y) = Σᵢy^{Aᵢ} with positions (observations) and directions (actions). Integrates Spivak/Niu Poly, Feigenbaum bifurcation, Mode 1/Mode 2, and GF(3) grading.
metadata:
  trit: 0
---

# polynomial-social-cognition

## The Core Insight

**"Agent" was hiding POLYNOMIAL STRUCTURE**

What we called "Agent" is actually a polynomial functor:

```
p(y) = Σ_{i ∈ p(1)} y^{p[i]}

p(1) = positions (states, observations, what I can perceive)
p[i] = directions (actions, responses from position i)
```

## Why Polynomial?

| Old concept | Polynomial equivalent |
|-------------|----------------------|
| Agent | `p ∈ Poly` |
| Agent state | Position `i ∈ p(1)` |
| Agent action | Direction `a ∈ p[i]` |
| Relationship | Lens morphism `p → q` |
| Coalition | Coproduct `p + q` |
| Hierarchy | Composition `p ◁ q` |
| Market | Tensor `p ⊗ q` |
| Institution | Quotient `p/~` |

## Mode 1 vs Mode 2 as Polynomials

```
Mode 1 (Innate, Fast, Subcortical):
    p₁(y) = 3y³
    
    3 positions: {threat, safe, ambiguous}
    3 directions each: {approach, freeze, avoid}
    
    FIXED polynomial - phylogenetically determined
    Fast because structure is precomputed (50ms)

Mode 2 (Interpretive, Slow, Prefrontal):
    p₂(y) = Σ_{c ∈ Context} y^{Actions(c)}
    
    Positions indexed by CONTEXT (variable)
    Directions depend on interpretation (learned)
    
    VARIABLE polynomial - ontogenetically acquired
    Slow because structure must be computed (200ms+)
```

## GF(3) as Polynomial Grading

```
The trit polynomial:

    𝟛(y) = y⁻¹ + y⁰ + y¹  =  y⁻¹ + 1 + y
         
    3 positions: {-1, 0, +1}
    Valence determines which sub-polynomial is active
    
Social polynomial as GF(3)-graded:

    p(y) = p₋₁(y) + p₀(y) + p₊₁(y)
    
    p₋₁ = avoid polynomial (threat responses)
    p₀  = neutral polynomial (observation)
    p₊₁ = approach polynomial (affiliation)
    
Conservation: morphisms preserve grading
    f: p → q  implies  Σ trits(p) ≡ Σ trits(q) (mod 3)
```

## Feigenbaum Bifurcation = Polynomial Insufficiency

At each social scale transition, the current polynomial operations become insufficient:

| Scale | n | Polynomial | New Structure Required |
|-------|---|------------|----------------------|
| Dyad | 2 | `p ⊗ p` | None (base case) |
| Triad | 3 | `p ⊗ p ⊗ p + Coalition` | Coproduct `+` |
| Band | 15 | `Σ_{rep} p^⊗n` | Σ-indexing |
| Tribe | 50 | `Π_{myth} (Σ_{rep} p^⊗n)` | Π-structure |
| Institution | 150+ | `p/~` | Quotient by role |

The Feigenbaum constant δ ≈ 4.669 measures the **rate** at which polynomial complexity must increase.

## Polynomial Operations

```python
from discopy.monoidal import Ty, Box

# Types
Poly = Ty('𝑝')           # Generic polynomial
Pos = Ty('Pos')          # Positions
Dir = Ty('Dir')          # Directions

# Operations
tensor = Box('⊗', Poly @ Poly, Ty('𝑝⊗𝑞'))      # Parallel (Market)
compose = Box('◁', Poly @ Poly, Ty('𝑝◁𝑞'))     # Wiring (Authority)
cosum = Box('+', Poly @ Poly, Ty('𝑝+𝑞'))       # Coproduct (Communal)
quotient = Box('/~', Poly, Ty('𝑝/∼'))          # Quotient (Institution)

# Relational models as polynomial morphisms
communal = Box('Communal', Poly @ Poly, Ty('(𝑝+𝑞)/∼'))
authority = Box('Authority', Poly @ Poly, Ty('𝑝◁𝑞'))
equality = Box('Equality', Poly @ Poly, Ty('𝑝⊗𝑞+swap'))
market = Box('Market', Poly @ Poly, Ty('𝑝⊗𝑞'))
```

## Trampoline as Lens Morphism

```
The Mode 1 ↔ Mode 2 trampoline is a lens:

    (get, put): p₂ ⇄ p₁
    
    get: p₂(1) → p₁(1)
        Compress context-indexed positions to 3 valence states
        (This is Mode 2 → Mode 1: FORGET)
        
    put: Σᵢ p₂[i] × p₁[get(i)] → p₂[i]
        Elaborate 3 actions to context-appropriate responses
        (This is Mode 1 → Mode 2: GENERATE)
```

## Wounded Cue = Partial Lens

```
Clean signal:   p → q is a LENS (total, invertible-ish)
Wounded signal: p → q is a PARTIAL lens (gaps in fiber)

Error correction strategies:
    Interpolate: Extend by nearby fibers (secure attachment)
    Mute: Send to terminal polynomial 1 (avoidant)
    Raw: Output the partiality as data (anxious)
```

## Connection to Spivak/Niu Poly

From David Spivak and Nelson Niu's work:

- **Poly** is the category of polynomial functors
- Morphisms are **lenses** (charts + cocharts)
- **⊗** (tensor) and **◁** (composition) form a duoidal structure
- Polynomial comonads model **dynamical systems**
- The **arena** perspective: positions = observations, directions = moves

## DiscoHy Integration

```clojure
;; discohy polynomial social cognition
(import discopy.monoidal [Ty Box])

(setv Poly (Ty "𝑝"))
(setv Mode1 (Ty "3y³"))
(setv Mode2 (Ty "Σ_c y^A(c)"))

;; Relational models
(setv communal (Box "Communal" (@ Poly Poly) (Ty "(𝑝+𝑞)/∼")))
(setv authority (Box "Authority" (@ Poly Poly) (Ty "𝑝◁𝑞")))
(setv market (Box "Market" (@ Poly Poly) (Ty "𝑝⊗𝑞")))

;; Bifurcation = adding polynomial structure
(defn bifurcate [p new-structure]
  (Box (+ "+" new-structure) p (Ty (+ "𝑝+" new-structure))))
```

## Mathpix Integration (for paper extraction)

This skill is designed for extracting polynomial/categorical structures from papers:

```python
# Extract polynomial formulas from paper images
from mathpix import extract_latex

# Look for patterns like:
# p(y) = Σ...
# Poly morphisms
# Lens diagrams
# Duoidal structure

POLYNOMIAL_PATTERNS = [
    r'p\(y\)\s*=',           # Polynomial definition
    r'\\Sigma.*y\^',          # Σ-indexed
    r'\\otimes|\\triangleleft', # Tensor/composition
    r'Poly|Arena|Lens',       # Category names
]
```

## GF(3) Triads

```
polynomial-social-cognition (0) ⊗ discohy-streams (-1) ⊗ gay-mcp (+1) = 0 ✓
feigenbaum-bifurcation (-1) ⊗ polynomial-social-cognition (0) ⊗ unworld (+1) = 0 ✓
```

## References

- Spivak, D. & Niu, N. - *Polynomial Functors: A General Theory of Interaction*
- Shapiro, B. & Spivak, D. - *Dynamic Categories, Dynamic Operads* (arXiv:2205.03906)
- Fiske, A. - *Structures of Social Life* (1991) - Relational models
- Friston, K. - Active inference as polynomial dynamics

## Files

- `/Users/bob/iii/src/feigenbaum_social_render.py` - DisCoPy implementation
- `/Users/bob/iii/src/feigenbaum_extended.py` - Bifurcation dynamics
- `/Users/bob/iii/src/discohy_feigenbaum_social.hy` - Hy implementation
- `/Users/bob/iii/src/feigenbaum_diagrams/` - Rendered diagrams

## Key Terminology Update

| Old Term | New Term | Polynomial |
|----------|----------|------------|
| Agent | Poly / Interface | `p(y)` |
| State | Position | `p(1)` |
| Action | Direction | `p[i]` |
| Relationship | Lens | `p → q` |
| Social network | Poly diagram | Composition of lenses |

## See Also

- `discohy-streams` - Operadic color streams
- `unworld` - Derivational pattern generation
- `gay-mcp` - GF(3) conservation
- `asi-polynomial-operads` - Polynomial + operads + open games
- `parametrised-optics-cybernetics` - Para(C) and agency


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
