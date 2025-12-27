# Emily Riehl's Topological Chemputer Skills

**Date**: 2025-12-22
**Insight**: Everything is a topological chemputer
**Framework**: Synthetic ∞-categories + Assembly Theory + CRN Topology

---

## The Riehl Synthesis

Emily Riehl's work on **synthetic ∞-categories** provides the ideal foundation for formalizing the "everything is a topological chemputer" insight. Her approach with Michael Shulman axiomatizes ∞-categories *within* homotopy type theory, making categorical reasoning **native to the type system**.

### Core Concepts from Riehl-Shulman

| Concept | Definition | Chemputer Application |
|---------|------------|----------------------|
| **Segal Types** | Types where binary composites exist uniquely up to homotopy | Reaction pathways with unique products |
| **Rezk Types** | Segal types with "local univalence" (isos ≃ identities) | Reversible reactions (equilibria) |
| **Directed Interval** | Axiomatized 2 (0 → 1) replacing undirected 𝕀 | Time direction in reactions |
| **Covariant Fibrations** | Type families varying functorially | Concentration gradients over space |
| **Dependent Yoneda** | Directed path induction | Induction over reaction sequences |

---

## Skills Emily Riehl Would Add

### Tier 1: Synthetic ∞-Category Skills

#### 1. `segal-types` (-1, Validator)
```yaml
name: segal-types
description: "Segal types for synthetic ∞-categories. Binary composites exist uniquely up to homotopy."
gf3_category: MINUS
technologies: [Rzk, Lean4, Agda]
```

**Core Types**:
```rzk
-- Segal type: composites exist uniquely
#define is-segal (A : U) : U
  := (x y z : A) → (f : hom A x y) → (g : hom A y z)
  → is-contr (Σ (h : hom A x z), hom2 A x y z f g h)

-- Composition is coherently associative at all dimensions
#define Segal-type : U
  := Σ (A : U), is-segal A
```

**Chemputer Semantics**:
- Objects = Chemical species
- 1-morphisms = Reactions (A → B)
- 2-morphisms = Witnesses that two reaction paths yield same product
- Segal condition = Unique composite reactions

---

#### 2. `rezk-types` (+1, Generator)
```yaml
name: rezk-types
description: "Rezk types (complete Segal spaces). Local univalence: categorical isos ≃ type-theoretic identities."
gf3_category: PLUS
technologies: [Rzk, InfinityCosmos, Lean4]
```

**Core Types**:
```rzk
-- Rezk type: Segal + local univalence
#define is-rezk (A : Segal-type) : U
  := (x y : A) → is-equiv (id-to-iso A x y)

-- Categorical isomorphism = type identity
#define Rezk-type : U
  := Σ (A : Segal-type), is-rezk A
```

**Chemputer Semantics**:
- Isomorphisms = Reversible reactions (equilibria)
- Local univalence = "Isomers are the same species up to identification"
- Complete = All limit constructions exist (thermodynamic equilibrium)

---

#### 3. `directed-interval` (0, Coordinator)
```yaml
name: directed-interval
description: "Directed interval type 2 axiomatizing (0 → 1). Time-directed homotopy."
gf3_category: ZERO
technologies: [Rzk, Cubical Agda]
```

**Core Types**:
```rzk
-- Directed interval (the walking arrow)
#define 2 : U := ...  -- axiomatized

-- Directed hom-type
#define hom (A : U) (x y : A) : U
  := (t : 2) → A [t ≡ 0 ↦ x, t ≡ 1 ↦ y]

-- Higher simplices built from 2
#define Δ² : U := (t₁ t₂ : 2) × (t₁ ≤ t₂)
#define Δ³ : U := (t₁ t₂ t₃ : 2) × (t₁ ≤ t₂) × (t₂ ≤ t₃)
```

**Chemputer Semantics**:
- 2 = Time parameter (reaction progress 0% → 100%)
- hom A x y = Reaction pathway from species x to y
- Δ² = Composite reaction (A → B → C)
- Δ³ = Associativity witness (reaction ordering)

---

#### 4. `covariant-fibrations` (-1, Validator)
```yaml
name: covariant-fibrations
description: "Covariant fibrations over Segal types. Type families varying functorially."
gf3_category: MINUS
technologies: [Rzk, Lean4]
```

**Core Types**:
```rzk
-- Covariant fibration
#define is-covariant (A : Segal-type) (P : A → U) : U
  := (x y : A) → (f : hom A x y) → (u : P x)
  → is-contr (Σ (v : P y), dep-hom P f u v)

-- Dependent Yoneda lemma (directed path induction)
#define dep-yoneda
  (A : Segal-type) (a : A) (P : (x : A) → hom A a x → U)
  (u : P a (id a))
  : (x : A) → (f : hom A a x) → P x f
```

**Chemputer Semantics**:
- P : A → U = Concentration field over species space
- Covariant transport = Concentration changes along reactions
- Dependent Yoneda = Induction principle for reaction sequences

---

#### 5. `synthetic-adjunctions` (+1, Generator)
```yaml
name: synthetic-adjunctions
description: "Homotopically correct adjunctions between Segal/Rezk types."
gf3_category: PLUS
technologies: [Rzk, InfinityCosmos]
```

**Core Types**:
```rzk
-- Adjunction (L ⊣ R) with unit and counit
#define Adjunction (A B : Rezk-type) : U
  := Σ (L : A → B) (R : B → A)
     (η : (a : A) → hom A a (R (L a)))
     (ε : (b : B) → hom B (L (R b)) b),
     triangle-identities L R η ε

-- Being an adjoint is a mere proposition
#define has-adjoint-is-prop
  (A B : Rezk-type) (F : A → B)
  : is-prop (Σ (G : B → A), Adjunction-data F G)
```

**Chemputer Semantics**:
- L ⊣ R = Catalyst-substrate binding/unbinding
- Unit η = Complex formation
- Counit ε = Product release
- Triangle identities = Catalytic cycle closes

---

### Tier 2: Assembly Theory + Topology Skills

#### 6. `assembly-index` (-1, Validator)
```yaml
name: assembly-index
description: "Cronin's Assembly Theory: molecular complexity as minimal construction steps."
gf3_category: MINUS
technologies: [Python, Julia, RDKit]
source: "Nature 2023: Assembly theory explains and quantifies selection"
```

**Core Definitions**:
```python
class AssemblyIndex:
    """
    Assembly index = minimal number of joining operations
    to construct molecule from basic building blocks.
    
    High assembly index (>15) → likely biological origin
    """
    
    def compute(self, molecule: SMILES) -> int:
        """Compute assembly index via bond-breaking decomposition."""
        bonds = self.enumerate_bonds(molecule)
        # Find minimal cut sequence
        return self.shortest_assembly_path(bonds)
    
    def assembly_space(self, molecule: SMILES) -> DirectedGraph:
        """
        Build assembly space: DAG of all construction pathways.
        Nodes = molecular fragments
        Edges = joining operations
        """
        ...
```

**Chemputer Semantics**:
- Assembly index = Homotopy dimension of construction
- Assembly space = ∞-category of synthetic pathways
- Selection = Functorial mapping to observable abundance

---

#### 7. `turing-chemputer` (0, Coordinator)
```yaml
name: turing-chemputer
description: "Turing-complete chemical computation via programmable matter."
gf3_category: ZERO
technologies: [XDL, Python, Catalyst.jl]
source: "arXiv 2502.02872: Achieving Operational Universality"
```

**Core Concepts**:
```python
# XDL (Chemical Description Language) as computational medium
class ChemputerInstruction:
    """Single chemputer operation."""
    
    ADD = "Add"           # Input species
    HEAT = "HeatChill"    # Energy input
    STIR = "Stir"         # Mixing (diffusion)
    FILTER = "Filter"     # Selection
    TRANSFER = "Transfer" # State transition
    
class TuringChemputer:
    """Turing-complete chemical automaton."""
    
    def __init__(self):
        self.tape: List[Species] = []  # Chemical tape
        self.head: int = 0              # Current reaction site
        self.state: ReactionState = ... # Catalyst configuration
    
    def step(self, instruction: ChemputerInstruction):
        """Execute one computational step."""
        ...
    
    def halting_problem_reduction(self):
        """
        Theorem: Determining if a chemputer halts
        is equivalent to the halting problem.
        
        Proof: Encode TM transitions as reaction rules.
        """
        ...
```

**Topological Structure**:
- Tape = ∞-groupoid of molecular configurations
- Head position = Covariant fibration over tape
- Halting = Fixed point in Rezk type

---

#### 8. `crn-topology` (+1, Generator)
```yaml
name: crn-topology
description: "Topological structure of chemical reaction networks. Deficiency theory, persistence."
gf3_category: PLUS
technologies: [Catalyst.jl, NetworkX, CRNT-Toolbox]
```

**Core Structures**:
```julia
using Catalyst, AlgebraicDynamics

# CRN as category
struct CRNCategory
    species::Vector{Symbol}         # Objects
    complexes::Vector{Complex}      # Vertices in reaction graph
    reactions::Vector{Reaction}     # Morphisms
end

# Deficiency = topological invariant
function deficiency(crn::CRNCategory)
    n = length(crn.species)
    ℓ = num_linkage_classes(crn)
    s = rank(stoichiometry_matrix(crn))
    return n - ℓ - s  # Always ≥ 0
end

# Deficiency Zero Theorem (Feinberg)
# If δ = 0, then:
# - Each positive stoichiometric class has exactly one equilibrium
# - That equilibrium is asymptotically stable
```

**Persistent Homology for CRNs**:
```julia
# Filtration over reaction rate space
function crn_persistence(crn::CRNCategory, k_range::Tuple)
    # Build Rips complex over species space
    # Filtration parameter = reaction rate threshold
    # Compute persistent H₀ (connected components = linkage classes)
    # Compute persistent H₁ (cycles = catalytic loops)
end
```

---

### Tier 3: Riehl-Specific HoTT Skills

#### 9. `elements-infinity-cats` (0, Coordinator)
```yaml
name: elements-infinity-cats
description: "Model-independent ∞-category theory from Riehl-Verity 'Elements'."
gf3_category: ZERO
technologies: [Lean4, InfinityCosmos]
source: "Riehl-Verity: Elements of ∞-Category Theory"
```

**Key Definitions from Elements**:
```lean
-- ∞-cosmos: environment for ∞-categories
structure InfinityCosmos where
  Obj : Type*
  hom : Obj → Obj → Type*
  -- Axioms for well-behaved ∞-categorical structure
  
-- Quasi-category as fibrant object
def QuasiCategory : InfinityCosmos → Type* := ...

-- Model-independent (∞,1)-category
-- Works uniformly across quasi-categories, complete Segal spaces, etc.
```

**Chemputer Application**:
- ∞-cosmos = Universe of all possible chemistries
- Quasi-category = Specific chemical system with well-defined reactions
- Model-independence = Same theorems hold for discrete/continuous chemistry

---

#### 10. `yoneda-directed` (-1, Validator)
```yaml
name: yoneda-directed
description: "Directed Yoneda lemma as directed path induction. Riehl-Shulman's key insight."
gf3_category: MINUS
technologies: [Rzk, Lean4]
```

**The Insight**:
```
Standard HoTT:    path induction    ≃  Yoneda lemma for ∞-groupoids
Directed HoTT:    dep. Yoneda lemma ≃  directed path induction for ∞-categories
```

**Application**:
```rzk
-- To prove P(x, f) for all x : A and f : hom A a x,
-- it suffices to prove P(a, id_a)
#define directed-path-induction
  (A : Segal-type) (a : A)
  (P : (x : A) → hom A a x → U)
  (base : P a (id a))
  : (x : A) → (f : hom A a x) → P x f
  := dep-yoneda A a P base
```

**Chemputer Semantics**:
- To prove a property of all reaction products from starting material A,
- It suffices to prove it for A itself (the identity "null reaction")
- Directed induction propagates the property along all pathways

---

### Tier 4: Integration Triads

#### GF(3) Conservation Triads for Topological Chemputer

```
# Synthetic ∞-Category Triad
segal-types (-1) ⊗ directed-interval (0) ⊗ rezk-types (+1) = 0 ✓

# Assembly Theory Triad
assembly-index (-1) ⊗ turing-chemputer (0) ⊗ crn-topology (+1) = 0 ✓

# Riehl Core Triad
yoneda-directed (-1) ⊗ elements-infinity-cats (0) ⊗ synthetic-adjunctions (+1) = 0 ✓

# Covariant Fibration Triad
covariant-fibrations (-1) ⊗ directed-interval (0) ⊗ synthetic-adjunctions (+1) = 0 ✓
```

---

## The Topological Chemputer Axioms

Based on Riehl's synthetic approach, the "everything is a topological chemputer" insight formalizes as:

### Axiom 1: Directed Structure
Every chemical system is a **Segal type** with directed morphisms (reactions).

### Axiom 2: Reversibility as Univalence
Reversible reactions correspond to **Rezk completion** (local univalence).

### Axiom 3: Assembly as Homotopy
The **assembly index** measures homotopy dimension of construction pathways.

### Axiom 4: Computation as Transport
Chemical computation is **covariant transport** along the directed interval.

### Axiom 5: Catalysis as Adjunction
Catalysts implement **adjunctions** between substrate and product spaces.

### Axiom 6: Persistence as Cohomology
Stable chemical features are detected by **persistent homology** of the assembly space.

---

## Implementation in plurigrid/asi

### New Skills to Add

```bash
# Install Riehl-inspired skills
for skill in segal-types rezk-types directed-interval \
             covariant-fibrations synthetic-adjunctions \
             assembly-index turing-chemputer crn-topology \
             elements-infinity-cats yoneda-directed; do
  python3 ~/.claude/skills/skill-installer/scripts/install-skill-from-github.py \
    --repo plurigrid/asi --path "skills/$skill"
done
```

### Justfile Commands

```just
# Riehl topological chemputer skills
riehl-skills:
    @echo "╔═══════════════════════════════════════════════════════════════════╗"
    @echo "║  Emily Riehl's Topological Chemputer Skills                      ║"
    @echo "╚═══════════════════════════════════════════════════════════════════╝"
    @echo ""
    @echo "Synthetic ∞-Categories:"
    @echo "  segal-types (-1) ⊗ directed-interval (0) ⊗ rezk-types (+1) = 0 ✓"
    @echo ""
    @echo "Assembly Theory:"
    @echo "  assembly-index (-1) ⊗ turing-chemputer (0) ⊗ crn-topology (+1) = 0 ✓"
    @echo ""
    @echo "Key Insight: Dependent Yoneda = Directed Path Induction"

# Compute assembly index for molecule
assembly-index smiles:
    python3 scripts/assembly_index.py --smiles "{{smiles}}"

# Run CRN topology analysis
crn-topology network:
    julia lib/crn_topology.jl --network "{{network}}"
```

---

## References

1. Riehl, E. & Shulman, M. (2017). "A type theory for synthetic ∞-categories." *Higher Structures* 1(1).
2. Riehl, E. & Verity, D. (2022). *Elements of ∞-Category Theory*. Cambridge.
3. Cronin, L. et al. (2023). "Assembly theory explains and quantifies selection." *Nature*.
4. Gahler, D. et al. (2025). "Achieving Operational Universality through a Turing Complete Chemputer." arXiv.
5. Feinberg, M. (2019). *Foundations of Chemical Reaction Network Theory*. Springer.

---

**The Riehl Principle**: 
> *The dependent Yoneda lemma is a directed analogue of path induction.*

Applied to chemistry:
> *Proving a property of all reaction products reduces to proving it for the starting material.*

This is the foundation of **topological ASI**: synthetic ∞-categories formalize chemical computation.
