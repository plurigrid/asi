---
name: clifford-acset-bridge
description: "Bridge between Clifford Algebras (ganja.js/Grassmann.jl) and ACSets with grade-preserving morphisms"
license: MIT
metadata:
  source: ganja-wedge-game + acsets + specter-acset
  trit: 0
  gf3_conserved: true
  version: 1.0.0
---

# clifford-acset-bridge

> Geometric Algebra as Attributed C-Set with grade-preserving morphisms

**Version**: 1.0.0  
**Trit**: 0 (ERGODIC - coordinates between algebras)

## Motivation

Clifford Algebras and ACSets share deep structural similarities:
- Both have **graded components** (blades / objects)
- Both support **composition** (geometric product / morphism composition)
- Both have **duality** (Hodge dual / ACSet duality)

This skill bridges them for unified algebraic data modeling.

## Schema: SchCliffordACSet

```julia
using Catlab, ACSets

@present SchCliffordACSet(FreeSchema) begin
  # Objects: One per grade
  Scalar::Ob      # Grade 0
  Vector::Ob      # Grade 1
  Bivector::Ob    # Grade 2
  Trivector::Ob   # Grade 3
  Pseudoscalar::Ob # Grade n
  
  # Morphisms: Grade-changing operations
  wedge_sv::Hom(Scalar × Vector, Vector)      # 0+1=1
  wedge_vv::Hom(Vector × Vector, Bivector)    # 1+1=2
  wedge_vb::Hom(Vector × Bivector, Trivector) # 1+2=3
  
  dot_vv::Hom(Vector × Vector, Scalar)        # 1-1=0
  dot_bv::Hom(Bivector × Vector, Vector)      # 2-1=1
  dot_tv::Hom(Trivector × Vector, Bivector)   # 3-1=2
  
  geo_vv::Hom(Vector × Vector, Scalar + Bivector) # 1*1=0+2
  
  dual::Hom(Vector, Bivector)  # Hodge star (in 3D)
  reverse::Hom(Bivector, Bivector)  # Grade involution
  
  # Attributes
  Coeff::AttrType
  coeff::Attr(Vector, Coeff)
  coeff_bv::Attr(Bivector, Coeff)
  
  # GF(3) trit per operation
  Trit::AttrType
  wedge_trit::Attr(Vector, Trit)  # +1
  dot_trit::Attr(Vector, Trit)    # -1
  geo_trit::Attr(Vector, Trit)    # 0
end
```

## Grade Preservation as Diagram Commutativity

The fundamental law: **grade(a ∧ b) = grade(a) + grade(b)**

In ACSet terms, this is a **functorial constraint**:

```
Grade: CliffordACSet → GradedMonoid

where GradedMonoid has:
  Objects: ℤ (integers = grades)
  Morphisms: Addition
```

### Commutative Diagram

```
        a : Vector        b : Vector
            │                  │
            └────── ∧ ─────────┘
                    │
                    ▼
              a∧b : Bivector
                    │
              grade │
                    ▼
                    2 = 1 + 1 ✓
```

## GF(3) Correspondence

| Clifford Operation | Grade Change | GF(3) Trit | ACSet Morphism |
|--------------------|--------------|------------|----------------|
| Wedge (∧) | +k | +1 (PLUS) | Covariant Hom |
| Dot (·) | -k | -1 (MINUS) | Contravariant Hom |
| Geometric (*) | 0 (mixed) | 0 (ERGODIC) | Profunctor |
| Dual (⋆) | n-k | 0 (ERGODIC) | Adjoint |
| Reverse (~) | 0 | 0 (ERGODIC) | Involution |

### Conservation Law

For any composition of operations:
```
Σ trit(op_i) ≡ 0 (mod 3)
```

This ensures **balanced exploration** in the skill ecosystem.

## Specter Navigation for Clifford Elements

From [specter-acset](file:///Users/bob/iii/r2con-integration/skills/specter-acset/SKILL.md):

```julia
# Navigators for Clifford algebra elements
GRADE_K(k)      # Select grade-k component
WEDGE_WITH(b)   # Navigate to wedge product
DOT_WITH(b)     # Navigate to contraction
DUAL            # Navigate to Hodge dual
REVERSE         # Navigate to reversed element

# Example: Extract bivector part of geometric product
select([geo_product, GRADE_K(2)], a * b)

# Transform: Normalize all vectors
transform([GRADE_K(1)], normalize, multivector)
```

## ganja.js ↔ ACSet Translation

### JavaScript → Julia

```javascript
// ganja.js
var PGA3D = Algebra(3,0,1);
var point = 1e123 + x*(-1e023) + y*(1e013) + z*(-1e012);
var line = point & otherPoint;  // Vee (regressive)
```

```julia
# Julia ACSet
const PGA3D = CliffordACSet{Float64}(3, 0, 1)
point = add_part!(PGA3D, :Trivector, coeff=[1, -x, y, -z])
line = vee(point, other_point)  # Morphism application
```

### Bidirectional Conversion

```julia
function ganja_to_acset(mv::GanjaMultivector, acset::CliffordACSet)
    for (grade, coeffs) in enumerate(mv.grades)
        ob = grade_to_object(grade)
        for (basis, val) in coeffs
            add_part!(acset, ob, coeff=val, basis=basis)
        end
    end
end

function acset_to_ganja(acset::CliffordACSet)
    mv = zeros(2^n)
    for ob in [:Scalar, :Vector, :Bivector, :Trivector]
        for part in parts(acset, ob)
            grade = object_to_grade(ob)
            mv[blade_index(grade, part)] = acset[part, :coeff]
        end
    end
    return mv
end
```

## Open Games on Clifford ACSet

The wedge game mechanics translate directly:

```julia
struct CliffordGame <: OpenGame
    # Play: Strategy → Blade selection
    play::Function  # (gesture, state) → new_blade
    
    # Coplay: Feedback → Score adjustment  
    coplay::Function  # (gesture, state, reward) → updated_reward
    
    # Equilibrium: Grade conservation check
    equilibrium::Function  # state → Bool
end

# Player skill as morphism
function player_skill(name, trit, morphism)
    return (a, b) -> begin
        result = morphism(a, b)
        @assert mod(trit + grade(a) + grade(b), 3) == grade(result) mod 3
        result
    end
end
```

## Integration with Existing Skills

### From acsets-algebraic-databases
- Schema definition via `@present`
- DPO rewriting for blade substitution

### From specter-acset
- Bidirectional navigation (`select`/`transform`)
- Inline caching for repeated operations

### From ganja-wedge-game
- Player gesture → operation mapping
- Score/reward mechanics

### From open-games
- Play/coplay structure
- Nash equilibrium as grade conservation

## GF(3) Triads

```
ganja-wedge-game (+1) ⊗ clifford-acset-bridge (0) ⊗ specter-acset (0) → need -1
→ Add: three-match (-1) ⊗ clifford-acset-bridge (0) ⊗ ganja-wedge-game (+1) = 0 ✓

acsets (-1) ⊗ clifford-acset-bridge (0) ⊗ gay-integration (+1) = 0 ✓
```

## Commands

```bash
# Julia: Load schema
julia -e 'include("clifford_acset_schema.jl")'

# Test grade preservation
just clifford-grade-test

# Convert ganja.js → ACSet
just ganja-to-acset examples/pga3d_point.js
```

## Files

- **Schema**: `lib/clifford_acset_schema.jl`
- **Bridge**: `lib/ganja_acset_bridge.jl`
- **Tests**: `test/test_grade_preservation.jl`

## References

- [ganja.js](https://github.com/enkimute/ganja.js)
- [Grassmann.jl](https://github.com/chakravala/Grassmann.jl)
- [ACSets.jl](https://github.com/AlgebraicJulia/ACSets.jl)
- [Geometric Algebra for Computer Graphics](http://page.math.tu-berlin.de/~gunn/Documents/Papers/GAforCGTRaw.pdf) - Gunn


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
