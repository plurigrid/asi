# Narya: Biggest Differences & Performance Expectations

**Author**: Emma (following Zubyul's patterns)
**Seed**: 137508
**Date**: 2025-12-30

---

## What Is Narya?

Narya is an **experimental proof assistant** for higher-dimensional type theory, implementing **Higher Observational Type Theory (HOTT)** — a third-generation approach distinct from both Book HoTT and Cubical Type Theory.

**Repository**: https://github.com/gwaithimirdain/narya
**Stars**: 216 | **Version**: v0.1 (Oct 2025)
**Language**: OCaml (95.8%)

---

## The Biggest Differences

### 1. Observational Equality (The Core Innovation)

| Approach | How Equality Works |
|----------|-------------------|
| **Book HoTT** | Identity types defined uniformly via induction |
| **Cubical** | Identity types defined by mapping from interval `I` |
| **Narya/HOTT** | Identity types defined **observationally per type** |

```
-- In Narya, equality is STRUCTURAL:
Id(A × B)(⟨x₀, y₀⟩, ⟨x₁, y₁⟩) ≡ Id_A(x₀, x₁) × Id_B(y₀, y₁)
Id(A → B)(f₀, f₁) ≡ (x : A) → Id_B(f₀ x, f₁ x)
```

**Impact**: Function extensionality is **definitional**, not axiomatic.

### 2. No Interval Required

| System | Interval? | Consequence |
|--------|-----------|-------------|
| Cubical Agda | Yes (`I : 𝔽`) | De Morgan algebra overhead |
| Rzk | Yes (shapes/topes) | Simplicial complexity |
| **Narya** | **No** | Simpler NbE, cleaner computation |

Narya encodes higher dimensions via:
- Implicit cube boundaries
- Degeneracy operations
- Bridge types for parametricity

### 3. Bridge Types (Internal Parametricity)

```narya
-- Bridge type: "baby equality" without symmetry/transitivity
Br(A) : A → A → Type

refl : (a : A) → Br A a a
map  : (f : A → B) → Br A a₁ a₂ → Br B (f a₁) (f a₂)
-- Note: NO sym, NO trans!
```

This gives **internal parametricity** — prove theorems about polymorphic functions without external axioms.

### 4. Definitional η-Laws

| Proof Assistant | Function η | Product η | Record η |
|-----------------|------------|-----------|----------|
| Agda | Postulate | Code trick | Field-wise |
| Coq | Axiom | Axiom | Convertible |
| Lean 4 | Axiom | Axiom | Projection |
| **Narya** | **Definitional** | **Definitional** | **Definitional** |

In Narya, `λx. f x` and `f` are **judgmentally equal** without postulates.

### 5. Type : Type (Currently)

Narya v0.1 has no universe hierarchy:
```narya
Type : Type  -- No level checking
```

This simplifies development but will be refined in future versions.

---

## Comparison Matrix

| Feature | Narya | Agda | Coq | Lean 4 | Rzk |
|---------|-------|------|-----|--------|-----|
| **Equality** | Observational | Intensional | Intensional | Intensional | Synthetic |
| **η-laws** | Definitional | Postulate | Postulate | Postulate | Definitional |
| **Interval** | None | None | None | None | Yes |
| **Parametricity** | Bridge types | External | External | External | Implicit |
| **Univalence** | Computes | Axiom | Axiom | Axiom | Computes |
| **Maturity** | Alpha | 35 years | 30 years | 10 years | Early |
| **Library size** | Nascent | Large | Huge | 90k+ thms | Small |

---

## Performance Expectations

### What We Know

| Metric | Narya | Comparison |
|--------|-------|------------|
| **Architecture** | NbE (Normalization by Evaluation) | Same as Agda |
| **Language** | Pure OCaml | Slower than Lean's C++ |
| **Caching** | `.nary` bytecode files | Incremental builds |
| **Web target** | jsNarya (WASM) | ~500KB gzipped |

### Expected Performance

| Scenario | Expected Time | Notes |
|----------|---------------|-------|
| **Small proofs** (< 100 lines) | < 1 second | Comparable to Agda |
| **Medium modules** (1000 defs) | Seconds | Untested at scale |
| **Large libraries** (10k+ defs) | Unknown | Likely 5-10x slower than Lean |

### Why No Formal Benchmarks?

1. **Experimental stage** — Premature optimization
2. **No large libraries** — Nothing to benchmark against
3. **Theory in flux** — Core features still changing
4. **OCaml vs C++** — Lean's kernel inherently faster

### Comparative Rankings (Estimated)

```
Performance (fast → slow):
  Lean 4 > Agda > Narya ≈ Cubical Agda > Coq

Equality clarity (best → worst):
  Narya > Cubical Agda > Rzk > Book HoTT > Lean/Coq

Library maturity (best → worst):
  Lean 4 > Coq > Agda >> Rzk > Narya
```

---

## GF(3) Triad for Proof Assistants

```
Type-theoretic innovation (+1 GENERATOR):
  Narya — pushing observational boundaries

Practical automation (0 COORDINATOR):
  Lean 4 — balancing theory with usability

Formal verification (-1 VALIDATOR):
  Coq — trusted, battle-tested kernel

Sum: +1 + 0 + (-1) = 0 ✓
```

---

## When to Use Narya

### Use Narya When:
- Researching observational equality
- Experimenting with parametricity
- Teaching HoTT without interval complexity
- Prototyping higher-dimensional proofs
- You want definitional function extensionality

### Don't Use Narya When:
- Production formal verification (use Lean/Coq)
- Large library development (use Agda/Lean)
- Need strong automation (use Lean/Coq)
- Stability is critical (use mature systems)

---

## Key Papers

1. **"Towards an Implementation of Higher Observational Type Theory"** (Shulman, 2024)
   - NbE algorithm details
   - https://home.sandiego.edu/~shulman/papers/running-hott.pdf

2. **"From parametricity to identity types"** (Altenkirch et al., 2025)
   - POTT foundations
   - https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper60.pdf

3. **"An observational proof assistant"** (Shulman, ASL 2025)
   - Latest overview
   - https://math.nmsu.edu/asl-2025/slides/asl-mike-2025.pdf

---

## Future Roadmap

| Phase | Feature | Status |
|-------|---------|--------|
| 1 | Parametric OTT (POTT) | ✓ Implemented |
| 2 | Higher OTT (HOTT) | In progress |
| 3 | Displayed Type Theory | Planned |
| 4 | Multi-modal extensions | Long-term |
| 5 | LSP / VS Code | 2025-2026 |

---

## Summary: The Three Key Differences

### 1. Observational > Intensional
Equality is defined **per type structure**, not uniformly. This makes extensionality automatic.

### 2. No Interval > Interval
Higher dimensions are implicit, not explicit. No De Morgan algebra overhead.

### 3. Bridge Types > External Parametricity
Parametricity is **internal** to the type theory, not a separate axiom.

---

*Emma's Note*: Narya represents what happens when you ask "what if equality were structural?" The answer turns out to be: most equality axioms become theorems, and computation becomes cleaner. The trade-off is maturity — Narya is research-grade, not production-ready.

**Seed**: 137508 | **Conservation**: Σ(trit) ≡ 0 (mod 3)
