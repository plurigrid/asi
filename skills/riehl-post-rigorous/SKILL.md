# Riehl Post-Rigorous Skill

Emily Riehl's post-rigorous mathematics framework: formalizing arguments that are "locally may contain errors but globally sound."

**Trit: 0 (ERGODIC)** — Coordinator between rigorous and synthetic approaches

## Core Thesis

> *"We thought we were post-rigorous but it may have turned out we also have been pre-rigorous as well, oy vey!"*

### The Triad of Mathematical Maturity (Tao)

```
PRE-RIGOROUS → RIGOROUS → POST-RIGOROUS
     ↓              ↓            ↓
  intuitive      formal      synthetic
  examples       proofs      sketches
  hand-waving    details     globally-sound
```

**Key Insight**: Post-rigorous mathematics allows "local errors that cancel globally" — this is GF(3) conservation: `(-1) + 0 + (+1) = 0`.

## Primary Sources

### Papers

| Paper | arXiv | Key Contribution |
|-------|-------|------------------|
| "Could ∞-category theory be taught to undergraduates?" | [2302.07855](https://arxiv.org/abs/2302.07855) | Formal vs axiomatic vs synthetic |
| "∞-category theory from scratch" | Higher Structures 4(1) | ∞-cosmos axiomatics |
| "Elements of ∞-Category Theory" | Cambridge Press | Model-independent foundations |
| "A type theory for synthetic ∞-categories" | with Shulman | Directed type theory |

### Talks

| Talk | Venue | Slides |
|------|-------|--------|
| "Formalizing post-rigorous mathematics" | Hausdorff Center 2024 | [PDF](https://emilyriehl.github.io/files/post-rigorous.pdf) |
| "Could we teach ∞-category theory to undergraduates or to a computer?" | Hardy Lecture 2025 | [PDF](https://emilyriehl.github.io/files/hardy-lecture.pdf) |
| "Prospects for formalizing ∞-category theory" | Birmingham 2025 | [PDF](https://emilyriehl.github.io/files/prospects-hardy.pdf) |
| "Contractibility as uniqueness" | UCLA 2024 | [PDF](https://emilyriehl.github.io/files/contractibility-as-uniqueness.pdf) |

## Three Formalization Strategies

### Strategy 1: CONCRETE (Analytic)

```
Formalize in specific model (quasi-categories in Lean)
└─ Labor-intensive but complete
└─ Example: mathlib4 category theory
└─ Pros: Fully rigorous, computable
└─ Cons: Model-specific, verbose
```

### Strategy 2: AXIOMATIC (∞-Cosmos)

```
Define ∞-cosmos axiomatically
└─ Prove theorems abstractly
└─ Show quasi-categories form ∞-cosmos
└─ Example: Elements of ∞-Category Theory
└─ Pros: Model-independent, elegant
└─ Cons: Requires axiom verification per model
```

### Strategy 3: SYNTHETIC (Domain-Specific Type Theory)

```
Generalized elements = terms in context
└─ Informal proof IS formal proof
└─ Example: Rzk proof assistant
└─ THIS IS THE POST-RIGOROUS APPROACH
└─ Pros: Natural, directly formalizable
└─ Cons: New foundations, learning curve
```

## Key Definitions (MathPix Extracted)

### ∞-Cosmos (Definition 1.2.1)

An **∞-cosmos** $\mathcal{K}$ is a simplicially enriched category with:

$$\mathcal{K} \text{ has } \begin{cases}
\text{(a) isofibrations closed under:} & \text{composition, pullback, cotensor} \\
\text{(b) limits of towers:} & A_0 \twoheadleftarrow A_1 \twoheadleftarrow A_2 \twoheadleftarrow \cdots \\
\text{(c) cotensors:} & A^X \text{ for } X \in \mathsf{sSet}
\end{cases}$$

**GF(3) Assignment**:
- Isofibration: trit = -1 (constraint/validation)
- Equivalence: trit = 0 (transport)
- Trivial fibration: trit = +1 (generation)

### Homotopy 2-Category (Definition 1.3.1)

The **homotopy 2-category** $\mathfrak{h}\mathcal{K}$ has:
- Objects: ∞-categories in $\mathcal{K}$
- 1-cells: ∞-functors
- 2-cells: Homotopy classes of natural transformations

$$\mathfrak{h}\mathcal{K}(A,B) := \pi_0(\mathrm{Fun}(A,B))$$

### Adjunction in ∞-Cosmos (Proposition 1.1.3)

An **adjunction** $f \dashv u$ in $\mathfrak{h}\mathcal{K}$ consists of:

$$\begin{CD}
A @>f>> B \\
@. @VuVV \\
@. A
\end{CD}
\quad \text{with } \eta: \mathrm{id}_A \Rightarrow uf, \quad \epsilon: fu \Rightarrow \mathrm{id}_B$$

satisfying triangle identities up to homotopy.

### Representable Terminal Element (Proposition 2.1.2)

An element $t: \mathbf{1} \to A$ is **terminal** iff:
$$\forall f: X \to A, \exists! \alpha: f \Rightarrow t \circ !$$

Diagrammatically:
```
     X
    f│   ⇓∃!
     ▼
1 ──t──▶ A
```

### Comma ∞-Category (Definition 3.1.1)

Given $f: A \to C$ and $g: B \to C$, the **comma ∞-category** $f \downarrow g$ satisfies:

$$\begin{CD}
f \downarrow g @>p_0>> A \\
@Vp_1VV @VfVV \\
B @>g>> C
\end{CD}$$

with a 2-cell $\phi: f p_0 \Rightarrow g p_1$ universal among such squares.

## Model Independence Theorem

**Theorem 3.6**: Categorical properties encoded by fibered equivalences between comma ∞-categories are:
1. **Preserved** by cosmological functors
2. **Reflected** by cosmological biequivalences

This includes:
- Adjunctions
- Limits/colimits
- Kan extensions
- Fibrations

## Proof Assistants

### Lean 4 (infinity-cosmos)

```lean
-- From plurigrid/infinity-cosmos
import InfinityCosmos.Basic

structure InfinityCosmos where
  carrier : Type*
  hom : carrier → carrier → QCat
  isofib : ∀ {A B}, (A ⟶ B) → Prop
  -- Axioms...

theorem model_independence (K₁ K₂ : InfinityCosmos) 
  (F : CosmologicalBiequiv K₁ K₂) :
  ∀ P : CategoricalProperty, P.holds_in K₁ ↔ P.holds_in K₂ := by
  sorry -- Main theorem
```

### Rzk (Synthetic)

```rzk
-- Synthetic ∞-category theory
#def is-segal (A : U) : U
  := (x y z : A) → (f : hom A x y) → (g : hom A y z)
     → is-contr (Σ (h : hom A x z), hom2 A x y z f g h)

#def yoneda-lemma (A : U) (is-segal-A : is-segal A)
  (a : A) (F : A → U) (is-covariant-F : is-covariant A F) :
  Equiv (F a) ((x : A) → hom A a x → F x)
  := ...
```

## GF(3) Conservation in Post-Rigorous

```
Strategy 1 (Concrete):  trit = -1  (rigorous validation)
Strategy 2 (Axiomatic): trit = 0   (model-independent transport)
Strategy 3 (Synthetic): trit = +1  (generative synthesis)

Conservation: (-1) + 0 + (+1) = 0 ✓
```

### Kapranov-Voevodsky Error Example

**Historical**: Claimed proof of a key lemma was later found incorrect.

**Post-rigorous insight**: The error was "local" — the global structure survived, and the gap was eventually filled by others.

**Skill analog**: If `skill-dispatch` and `dynamic-sufficiency` have inconsistent coverage requirements, formalization reveals the gap via bisimulation game.

## Hatchery Integration

| Repo | Color | Role |
|------|-------|------|
| `plurigrid/infinity-cosmos` | #90269E | Lean 4 formalization |
| `TeglonLabs/narya` | #3A71C0 | Higher observational TT |
| `emilyriehl/yoneda` | — | Rzk formalization project |
| `rzk-lang/rzk` | — | Synthetic proof assistant |

## World Connections

| World | Post-Rigorous Role |
|-------|-------------------|
| **A** (AlgebraicJulia) | ACSet as ∞-presheaf in ∞-cosmos |
| **B** (bmorphism) | Color-coded proof states |
| **E** (∞-categories) | Primary formalization target |

## MathPix Pipeline

```bash
# Extract diagrams from Riehl papers
mathpix convert_document \
  --path "elements-infinity-category-theory.pdf" \
  --formats latex \
  --checkpoint-seed 1069

# Convert to ACSet schema
julia -e '
using MathpixACSet
acset = pdf_to_acset("riehl-verity-scratch.pdf",
  seed=0x42D,
  checkpoint_pattern=SEED_1069)
'
```

### Key Diagram Extraction

```latex
% Homotopy 2-category
\begin{tikzcd}
A \ar[r, "f"] \ar[d, "g"'] & B \ar[d, "h"] \\
C \ar[r, "k"'] & D
\ar[from=1-1, to=2-2, Rightarrow, shorten <=3pt, shorten >=3pt, "\alpha"]
\end{tikzcd}

% Comma category universal property
\begin{tikzcd}
f \downarrow g \ar[r, "p_0"] \ar[d, "p_1"'] & A \ar[d, "f"] \\
B \ar[r, "g"'] & C
\ar[from=1-1, to=2-2, Rightarrow, shorten <=5pt, shorten >=5pt, "\phi"]
\end{tikzcd}
```

## Triadic Skill Integration

```
elements-infinity-cats (-1) ⊗ riehl-post-rigorous (0) ⊗ infinity-topos (+1) = 0 ✓
```

| Skill | Trit | Role |
|-------|------|------|
| `elements-infinity-cats` | -1 | Riehl-Verity foundations |
| `riehl-post-rigorous` | 0 | Coordinator/thesis |
| `infinity-topos` | +1 | ∞-topos extensions |

## Commands

```bash
# Fetch latest slides
curl -O https://emilyriehl.github.io/files/post-rigorous.pdf

# Convert to LaTeX
mathpix smart_pdf_batch --path post-rigorous.pdf

# Verify in Rzk
rzk typecheck synthetic-proof.rzk

# Check in Lean
lake build InfinityCosmos
```

## References

- Riehl, E. (2024). "Formalizing post-rigorous mathematics." Hausdorff Center.
- Riehl, E. (2023). "Could ∞-category theory be taught to undergraduates?" arXiv:2302.07855.
- Riehl, E. & Verity, D. (2020). "∞-category theory from scratch." Higher Structures 4(1).
- Riehl, E. & Verity, D. (2022). *Elements of ∞-Category Theory*. Cambridge.
- Riehl, E. & Shulman, M. (2017). "A type theory for synthetic ∞-categories." Higher Structures 1(1).
- Tao, T. (2007). "There's more to mathematics than rigour and proofs."


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
