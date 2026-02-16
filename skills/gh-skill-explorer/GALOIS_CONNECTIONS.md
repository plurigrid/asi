# 🔗 GALOIS CONNECTIONS: Missed Adjunctions in Discovered Repos

> *Finding the left-right pairs that unify disparate domains*

## Overview

A **Galois connection** is an adjunction between posets (or more generally, an adjunction between categories). When we find Galois connections between domains, we discover deep structural relationships that enable **information-preserving translation**.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         ADJUNCTION STRUCTURE                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│      L: A → B    (left adjoint - "free" construction)                       │
│      R: B → A    (right adjoint - "forgetful" or "underlying")              │
│                                                                              │
│      L ⊣ R   means:   Hom(L(a), b) ≅ Hom(a, R(b))                           │
│                                                                              │
│      Unit:   η: id_A → R ∘ L    (embed A into image of round-trip)          │
│      Counit: ε: L ∘ R → id_B    (project back from round-trip)              │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## ✅ CONFIRMED ADJUNCTIONS (from DeepWiki)

### 1. DisCoPy: Cup/Cap as Unit/Counit
**Source**: `discopy/discopy` rigid categories

```
Left adjoint:   a.l  (left dual)
Right adjoint:  a.r  (right dual)

Cup: a ⊗ a.r → I    (counit ε)
Cap: I → a.l ⊗ a    (unit η)

Snake equations: (id_a ⊗ cup) ∘ (cap ⊗ id_a) = id_a
```

**Implication**: Every type has bidirectional translation via cups/caps.

---

### 2. HoTT: Limit/Colimit Adjunction
**Source**: `HoTT/Coq-HoTT` Categories/Limits

```
Colimit functor:  L: Diagram(J,C) → C   (left adjoint)
Diagonal functor: Δ: C → Diagram(J,C)   
Limit functor:    R: Diagram(J,C) → C   (right adjoint)

L ⊣ Δ ⊣ R
```

**Implication**: Colimits freely construct, limits universally project.

---

### 3. CEREBRUM: Nom-Acc ⇄ Erg-Abs Alignment
**Source**: `ActiveInferenceInstitute/CEREBRUM` case system

```
F: CaseModel_Nom-Acc → CaseModel_Erg-Abs
G: CaseModel_Erg-Abs → CaseModel_Nom-Acc

F ⊣ G (morphosyntactic alignment adjunction)
```

**Implication**: Linguistic alignment systems are interchangeable via adjunction.

---

### 4. HoTT: Unit/Counit Adjunction Formalization
**Source**: `HoTT/Coq-HoTT` WildCat/Adjoint

```haskell
-- Hom-set adjunction
equiv_adjunction : (F x $-> y) <~> (x $-> G y)

-- Derived unit/counit
adjunction_unit : 1_C → G ∘ F
adjunction_counit : F ∘ G → 1_D

-- Triangle identities satisfied
adjunction_triangle1, adjunction_triangle2
```

**Implication**: Full categorical machinery for building new adjunctions.

---

## 🔍 IMPLICIT ADJUNCTIONS (inferred from structure)

### 5. GraphCast: Grid2Mesh ⊣ Mesh2Grid (Weak)
**Source**: `google-deepmind/graphcast`

```
Grid2Mesh: GridNodes → MeshNodes × LatentGridNodes  (encoder)
Mesh2Grid: MeshNodes × LatentGridNodes → GridNodes  (decoder)

NOT a strict adjunction, but:
- Grid2Mesh "freely" embeds grid into mesh representation
- Mesh2Grid "forgets" mesh structure back to grid
- Encoder-decoder pair with learned round-trip
```

**Implication**: Could be formalized as a lax adjunction or Kan extension.

---

### 6. Composio: Discovery ⊣ Execution (Operational)
**Source**: `ComposioHQ/composio`

```
Discovery: NLQuery → FilteredToolSet  (left - expands possibilities)
Execution: FilteredToolSet → Results  (right - collapses to outcomes)

Schema_D: All_Tools → Visible_Tools   (filtering)
Schema_E: Visible_Tools → Executed    (focusing)
```

**Implication**: Tool routing as resource management adjunction.

---

### 7. GFlowNets: Forward ⊣ Backward Policy (Flow Matching)
**Source**: `zdhNarsil/Awesome-GFlowNets` (theoretical)

```
Forward policy:  P_F(s'|s)   (generates trajectories)
Backward policy: P_B(s|s')   (traces back)

Flow matching: F(s) × P_F(s'|s) = F(s') × P_B(s|s')

At terminal: F(s) = R(s)
```

**Implication**: Detailed balance as a form of adjoint relationship.

---

### 8. Particle-Life: Attraction ⊣ Repulsion (Physical Duality)
**Source**: `hunar4321/particle-life`

```
Attraction(G > 0): particles → clusters   (aggregation)
Repulsion(G < 0):  clusters → dispersal   (separation)

Matrix symmetry: If G[a,b] is attraction, consider G[b,a]
```

**Implication**: Interaction matrix as bilinear pairing; dual forces.

---

## 🆕 NEWLY DISCOVERED REPOS WITH GALOIS STRUCTURES

| Repo | Stars | Galois/Adjunction Feature |
|------|-------|---------------------------|
| [cmk/connections](https://github.com/cmk/connections) | 6 | Numerical conversions via Galois connections |
| [AlgebraicJulia/Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl) | 681 | Full adjunction machinery |
| [haskellari/lattices](https://github.com/haskellari/lattices) | 35 | Lattice primitives, Galois connections |
| [sellout/haskerwaul](https://github.com/sellout/haskerwaul) | 19 | Category theory typeclasses |
| [nikita-volkov/lawful-conversions](https://github.com/nikita-volkov/lawful-conversions) | 5 | Lawful type conversions |
| [scheinerman/Posets.jl](https://github.com/scheinerman/Posets.jl) | 8 | Posets compatible with Graphs.jl |
| [AlgebraicJulia/AlgebraicRelations.jl](https://github.com/AlgebraicJulia/AlgebraicRelations.jl) | - | Relational algebra |
| [AlgebraicJulia/ACSets.jl](https://github.com/AlgebraicJulia/ACSets.jl) | 25 | Algebraic databases |

---

## Cross-Domain Galois Connections

### Connection 1: DisCoPy ↔ HoTT via Categorical Adjunctions

```
DisCoPy rigid categories     HoTT WildCat
        │                          │
        └──── Adjoint Functors ────┘
        
Cup/Cap (unit/counit)  ≃  η/ε (unit/counit)
Snake equations       ≃  Triangle identities
```

**Bridge**: Both formalize adjunctions; DisCoPy is computational, HoTT is foundational.

---

### Connection 2: CEREBRUM ↔ GFlowNets via Flow Optimization

```
CEREBRUM free energy          GFlowNets flow matching
        │                            │
        └─── Minimize divergence ────┘
        
Case transitions  ≃  Trajectory steps
Precision         ≃  Flow normalization
Belief updating   ≃  Backward policy
```

**Bridge**: Both minimize surprise/divergence via dynamics.

---

### Connection 3: Catlab ↔ DisCoPy via Applied Category Theory

```
Catlab.jl (Julia)            DisCoPy (Python)
        │                          │
        └─── Monoidal Categories ──┘
        
GATs / Theories   ≃  Grammar formalisms
Wiring diagrams   ≃  String diagrams
ACSet morphisms   ≃  Diagram functors
```

**Bridge**: Same mathematics, different implementation languages.

---

## Galois Connection Detection Algorithm

```python
def detect_galois_connection(domain_a: dict, domain_b: dict) -> dict:
    """
    Detect potential Galois connections between domains.
    
    A Galois connection exists if:
    1. There's a pair of opposing operations (L, R)
    2. L preserves structure in one direction
    3. R preserves structure in reverse
    4. L ∘ R and R ∘ L are monotone/coherent
    """
    result = {
        "left_adjoint": None,
        "right_adjoint": None,
        "unit": None,
        "counit": None,
        "evidence": []
    }
    
    # Check for encoder/decoder pairs
    if has_encoder_decoder(domain_a, domain_b):
        result["left_adjoint"] = "encoder"
        result["right_adjoint"] = "decoder"
        result["evidence"].append("encoder-decoder pair")
    
    # Check for free/forgetful pairs
    if has_free_forgetful(domain_a, domain_b):
        result["left_adjoint"] = "free"
        result["right_adjoint"] = "forgetful"
        result["evidence"].append("free-forgetful pair")
    
    # Check for cup/cap structures
    if has_dual_structure(domain_a):
        result["unit"] = "cap"
        result["counit"] = "cup"
        result["evidence"].append("rigid category duals")
    
    return result
```

---

## Integration with Harmonization Engine

```python
# Add to harmonize.py

GALOIS_CONNECTIONS = {
    ("discopy", "hott"): {
        "type": "categorical-adjunction",
        "left": "cup-cap structure",
        "right": "unit-counit formalization",
        "bridge": "Both formalize adjunctions differently"
    },
    ("cerebrum", "gflownet"): {
        "type": "flow-optimization",
        "left": "free-energy minimization",
        "right": "flow-matching",
        "bridge": "Both minimize divergence via dynamics"
    },
    ("graphcast", "discopy"): {
        "type": "encoder-decoder",
        "left": "Grid2Mesh (encode)",
        "right": "Mesh2Grid (decode)",
        "bridge": "Compositional message-passing"
    },
}

def find_galois_bridges(domain_a: str, domain_b: str) -> dict:
    """Find Galois connection bridge between domains."""
    key = (domain_a, domain_b)
    return GALOIS_CONNECTIONS.get(key) or GALOIS_CONNECTIONS.get((domain_b, domain_a))
```

---

## Next Steps

1. **Index cmk/connections** - Explicit Galois connection library
2. **Index Catlab.jl** - Full AlgebraicJulia adjunction machinery
3. **Formalize GraphCast** - Make encoder-decoder a proper adjunction
4. **Unify CEREBRUM + GFlowNets** - Flow-based adjunction framework
5. **Build Galois bridge detector** - Automated discovery of cross-domain adjunctions

---

## New Skill: galois-connections

Created `/Users/bob/.claude/skills/galois-connections/` with:

- `SKILL.md` - Behaviors lifted from cmk/connections
- `galois.py` - Python implementation with floor/ceiling/round/truncate

### Key Behaviors Lifted

| Behavior | Adjoint | Description |
|----------|---------|-------------|
| `floor` | Left (f) | Greatest lower bound: max { y : f(y) ≤ x } |
| `ceiling` | Right (h) | Least upper bound: min { y : x ≤ g(y) } |
| `round` | Middle (g) | Nearest value (adjoint string f ⊣ g ⊣ h) |
| `truncate` | Conditional | Floor if x≥0, ceiling if x<0 |
| `outer` | Both | Bounding interval (floor, ceiling) |
| `inner` | Exact | Exact representation if possible |
| `lift` | Compose | Compute in higher precision, round back |

### Usage

```bash
uv run galois.py list           # Show connections
uv run galois.py all 3.7        # All conversions for 3.7
uv run galois.py rational "1/7" # Rational → Float analysis
uv run galois.py verify         # Verify adjunction properties
```
