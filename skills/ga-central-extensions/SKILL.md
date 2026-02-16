# GA Central Extensions Skill

Central extensions of rotation groups via Clifford algebras and spinor covering spaces.

**Trit: 0 (ERGODIC)** — Transport/coordination between Lie algebra and Lie group

## Mathematical Foundation

### The Fundamental Central Extension

```
1 → ℤ/2 → Spin(n) → SO(n) → 1
        ↓        ↓        ↓
      (-1)    Motors   Rotations
```

This is THE central extension: Spin(n) is the universal cover of SO(n).

### Pin and Spin Groups from Clifford

```
Pin(V,Q) = {v₁v₂...vₖ ∈ Cl(V,Q) : vᵢ ∈ V, Q(vᵢ) = ±1}
Spin(V,Q) = Pin(V,Q) ∩ Cl⁺(V,Q)  -- even subalgebra

Central element: -1 ∈ Spin(n) maps to 1 ∈ SO(n)
Kernel = ℤ/2 = center of extension
```

### Exp/Log as Extension Witness

```
                exp
    spin(n) ────────→ Spin(n)
       ↓                ↓ π
    so(n) ─────────→ SO(n)
               exp

Bivector B ∈ Cl² ≅ spin(n)
Motor M = exp(B/2) ∈ Spin(n)
Rotation R = π(M) ∈ SO(n)
```

## ACSet Schema for Central Extensions

```julia
@present SchCentralExtGA(FreeSchema) begin
  # Objects in extension sequence
  (Kernel, TotalGroup, BaseGroup)::Ob
  (LieAlg_K, LieAlg_T, LieAlg_B)::Ob
  
  # Group morphisms
  inject::Hom(Kernel, TotalGroup)      # ℤ/2 → Spin
  project::Hom(TotalGroup, BaseGroup)  # Spin → SO
  
  # Lie algebra morphisms
  d_inject::Hom(LieAlg_K, LieAlg_T)    # 0 → spin (kernel is discrete)
  d_project::Hom(LieAlg_T, LieAlg_B)   # spin ≅ so (isomorphism!)
  
  # Exp/Log connecting group ↔ algebra
  exp_total::Hom(LieAlg_T, TotalGroup)  # bivector → motor
  log_total::Hom(TotalGroup, LieAlg_T)  # motor → bivector
  
  # Central element
  central::Attr(Kernel, Sign)  # -1 ∈ Spin
  
  # GF(3): centrality condition
  trit::Attr(TotalGroup, GF3Trit)
end
```

## H²(G, A) Classification

Central extensions classified by group cohomology H²(G, A):
```
H²(SO(n), ℤ/2) ≅ ℤ/2 for n ≥ 3

[0] = trivial extension SO(n) × ℤ/2
[1] = Spin(n) (non-trivial, connected double cover)
```

### GF(3) Cohomology Lift

```
H²(SO(n), ℤ/3) classifies ℤ/3-central extensions
- Relevant for GF(3) trit extensions
- Trivial for most SO(n), but structure preserved

Skill triad cohomology:
H²(SkillTriad, GF(3)) ≅ GF(3)
[0]: balanced triad (sum = 0)
[±1]: unbalanced (needs completion)
```

## Motor Decomposition (from pga-motor-interpolation)

```julia
# Motor M ∈ Spin⁺(3,0,1) decomposes:
struct MotorDecomp
    scalar::Float64      # cos(θ/2), trit = -1
    bivector::Vec3       # sin(θ/2)·axis, trit = 0  
    ideal_biv::Vec3      # translation, trit = +1
end

# Central extension structure:
# M and -M project to same rotation
# π(M) = π(-M) ∈ SE(3)
```

## Spinor Representations

```
Spinors = representations of Spin(n) that DON'T descend to SO(n)

Cl(n) acts on spinor space S
dim(S) = 2^⌊n/2⌋

The "square root of geometry" — needs double cover to define
```

## Integration with GA Skills

| Skill | Central Extension Role | Trit |
|-------|----------------------|------|
| ga-abelian-extensions | Ext functor framework | -1 |
| **ga-central-extensions** | Spin covers, H² | 0 |
| ga-derived-category | Derived functors | +1 |

**Triad**: (-1) + 0 + (+1) = 0 ✓

## Open Games: Covering as Strategy

```
Play:   SO(n) → Spin(n)     -- "lift rotation to motor"
Coplay: Motor → (±1, R)     -- "project with sign ambiguity"

Equilibrium: consistent sign choice = spin structure
Obstruction: w₂ (2nd Stiefel-Whitney class)
```

## Specter Navigation

```clojure
;; Lift through central extension
(defn lift-to-spin [rotation]
  (sp/transform [MOTOR-PATH]
    #(choose-sign % (orientation-context))
    (exp-map (log-so rotation))))

;; Descend to SO
(sp/select [ALL :project] spin-element)
```

## Commands

```bash
# Compute spin lift of rotation
julia -e 'spin_lift(rotation_matrix(π/4, [1,0,0]))'

# Check if manifold admits spin structure
bb -e '(spin-structure? manifold-acset)'

# H² computation
julia -e 'group_cohomology(SO(3), ZZ/2, 2)'
```

## References

- Lawson & Michelsohn: Spin Geometry (Ch. 1)
- Lounesto: Clifford Algebras and Spinors
- pga-motor-interpolation skill (Exp/Log maps)
- ga-abelian-extensions skill (Ext framework)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
