# Post-Rigorous Mathematics & Formalization: Complete Resource Guide

---

## I. FOUNDATIONAL REFERENCES

### On Post-Rigorous Mathematics

**Primary Source:**
- Terry Tao's Blog Post (date not specified in talk, but cited as "famous")
  - Defines three stages of mathematical development
  - Advocates post-rigorous as aspirational ideal
  - Identifies error patterns specific to post-rigorous work

### On Formalization in Mathematics

**Key Papers & Works:**
- Kapranov & Voevodsky (1991): "Infinity Groupoids and Homotopy Types"
  - First rigorous treatment of homotopy hypothesis
  - Contains subtle errors identified much later by Simpson
  - Motivates Voevodsky's move to formal verification

- Carlos Simpson (1998): Preprint on 3-type of S²
  - Shows contradiction with Kapranov-Voevodsky
  - Demonstrates difficulty of error detection in complex mathematics

- Jacob Lurie: "On Infinity Topoi" (preprint)
  - Deliberately post-rigorous: avoids precise definition of infinity categories
  - Led to development of "Higher Topos Theory" (later, more rigorous)
  - Illustrates community pressure toward rigor

- Jacob Lurie: "Higher Topos Theory" (book)
  - Formal treatment using quasi-categories
  - Concrete model of abstract infinity category theory

- Baez & Dolan (1990s): Cobordism Hypothesis
  - Classified fully extended topological quantum field theories
  - "Proved" by Hopkins-Lurie (dim 2) and Lurie (higher dims)
  - Proof exists only as detailed sketch (preprint)
  - Unclear if formally proven or still conjectural

- Gaitsgory & Rozenblyum: Derived Algebraic Geometry (2 volumes, 1000+ pages)
  - Explicitly marks 7 unproven statements
  - Model for transparent gap-marking
  - Spawned substantial follow-up research

### On Infinity Category Theory

**Foundational Works:**
- Emily Riehl & Dominic Verity: "Elements of ∞-Category Theory"
  - Uses Infinity Cosmos framework (Strategy 2)
  - Covers pullbacks, pushouts, fibers, cofibers synthetically
  - Emphasizes generalized elements and coherence

**Modern Formalization:**
- Emily Riehl (recent): Formalizing ∞-category theory in Rzk
  - Synthetic approach (Strategy 3)
  - Uses domain-specific type theory
  - Makes informal and formal proofs align naturally

---

## II. PEOPLE & INSTITUTIONS

### Key Figures

**Mathematicians:**
- Terry Tao: Conceptualized post-rigorous mathematics
- Emily Riehl: Modern infinity category theory, formalization advocate
- Jacob Lurie: Foundational infinity category theory
- Vladimir Voevodsky: Formal verification pioneer, HoTT developer
- Carlos Simpson: Identified subtle errors in infinity category literature
- Valery Isaev: Mentioned for Rzk proof assistant work
- Gaitsgory & Rozenblyum: Transparent about gaps in derived algebraic geometry

**Research Communities:**
- Hausdorff Center for Mathematics: hosting venue
- Topos Institute: connected research
- Institute for Advanced Study: Voevodsky's institution during formalization work

### Institutions & Venues

- Hausdorff Center for Mathematics (Bonn)
- arXiv: primary preprint repository for mathematics
- MathOverflow: community Q&A (2023 question on cobordism hypothesis status)

---

## III. PROOF ASSISTANTS & FORMALIZATION TOOLS

### Lean & Mathlib

**Framework:** Set-theory based (ZFC), most mature ecosystem

**Strengths:**
- Extensive library (mathlib)
- Large community
- Practical for concrete mathematics
- Can formalize Strategy 1 (concrete model)

**Current State:**
- Quasi-categories being formalized in mathlib
- Natural number game and other learning resources
- Active community formalizing mathematical results

**Relevant for:**
- Formalizing specific models of infinity categories
- Concrete category theory proofs

---

### Rzk (Proof Assistant for Synthetic ∞-Categories)

**Framework:** Synthetic type theory, domain-specific

**Purpose:**
- Designed specifically for infinity category theory
- Avoids set-theoretic technicalities
- Aligns informal and formal proofs naturally

**Strengths:**
- Element-wise proofs are rigorous by design
- More natural for working mathematicians
- Matches intuitive mathematical reasoning

**Current Development:**
- Emily Riehl: formalizing foundations of ∞-category theory
- Generalized elements as first-class citizens
- Growing library of infinity category constructs

**Relevant for:**
- Strategy 3 (synthetic approach)
- Infinity category theory as primary domain
- Projects where natural presentation matters

---

### Coq

**Framework:** Constructive type theory, general purpose

**Current State:**
- Used for some infinity category work
- Less specialized than Rzk but more general than Lean for this purpose

---

## IV. FORMALIZATION FRAMEWORKS

### Strategy 1: Concrete Model in Set Theory

**Approach:** Use specific model (quasi-categories, simplicial sets, etc.)

**Tools:** Lean, Coq, Isabelle

**When to Use:**
- Have a specific model in mind
- Need practical, working formalization quickly
- Other tools dependent on concrete constructions

**Challenges:**
- Must choose model early
- Separate proofs needed for other models
- Scale limitations for higher categories

**Economics:** High implementation cost, medium payoff

---

### Strategy 2: Infinity Cosmos (Abstract Framework)

**Approach:** Define abstract axioms, prove theorems once, reuse across models

**Reference Implementation:**
- Riehl & Verity: "Elements of ∞-Category Theory"
- Chapter 4: "Defining Infinity Categories"
- Chapters 1-3: How to define pullback, pushout, fiber, cofiber in cosmos

**Mathematical Objects:**
- Infinity Cosmos (abstract axioms)
- Infinity categories as objects in cosmos
- Examples: quasi-categories, complete Segal spaces, etc.

**When to Use:**
- Multiple models needed
- Want theorems to work across frameworks
- Can invest in axiomatization

**Advantages:**
- Theorems proven once
- Automatic transfer to new models
- Matches mathematical community practice

**Challenges:**
- Proving models exist is hard
- Requires axiomatic design skill
- May not capture all desired properties

**Economics:** Very high upfront cost (proving models exist), massive payoff (all theorems transfer for free)

---

### Strategy 3: Synthetic Type Theory

**Approach:** Develop theory in domain-specific type theory, avoid set-theoretic translation

**Reference Implementation:**
- Rzk proof assistant
- Emily Riehl's ongoing formalization work

**Key Idea:**
- Generalized elements = terms in context (not separate objects)
- Element-wise proofs become rigorous
- Informal and formal align naturally

**When to Use:**
- Domain is fixed (infinity categories)
- Natural presentation matters greatly
- Willing to use specialized tools
- Have expertise in type theory

**Advantages:**
- Informal mathematical reasoning is formally valid
- Smaller gap between intuition and proof
- Natural for practiced mathematicians

**Challenges:**
- Requires bespoke proof assistant
- Harder to integrate with other domains
- Smaller ecosystem

**Economics:** Different tradeoff—accept specialized tools for natural alignment

---

## V. MATHEMATICAL CONCEPTS TO FORMALIZE

### Core Definitions

**Initial & Terminal Objects:**
- Post-rigorous: "exist unique morphisms to/from any object"
- Rigorous: Requires careful universal property definition
- Formal: Universal property quantified over all objects

**Fiber & Cofiber:**
- Post-rigorous: "pullback and pushout of a morphism"
- Rigorous: Requires handling of base change and composition
- Formal: Must be defined internally to category, handle coherence

**Stable Infinity Categories:**
- Definition: pointed, every morphism has fiber & cofiber, they coincide
- Challenge: "coincide" means pullback and pushout squares are equivalent
- Formalization: Equivalence in higher categorical sense (not strict equality)

**Pullback Composition & Cancellation:**
- Post-rigorous: "by pullback cancellation..."
- Rigorous: Explicit statement of how pullbacks compose
- Formal: Proving diagram commutativity at all higher levels

### Higher Categorical Structures

- Infinity groupoids vs. homotopy types (homotopy hypothesis)
- Infinity n-categories (n>1, complexity increases dramatically)
- Higher morphisms and coherence
- Completeness and saturation conditions

---

## VI. CASE STUDIES FOR FORMALIZATION

### Recommended Entry Points

**Simple (Strategy 1):**
- Basic category theory (objects, morphisms, functors)
- Pullbacks and pushouts in classical categories
- Adjoint functors
- Kan extensions (though higher categorical version is hard)

**Intermediate (Strategy 2):**
- Basics of infinity categories (definition via axioms)
- Stable infinity categories
- Derived functors
- Homotopy types and fundamental groups

**Advanced (Strategy 3 or 2):**
- Infinity topoi
- Fully extended TQFTs (cobordism hypothesis)
- Derived algebraic geometry
- Higher category theory of categories

---

## VII. COMMON PITFALLS & HOW FORMALIZATION HELPS

### Pitfall 1: Hidden Assumptions
**Problem:** Literature assumes reader expertise to fill gaps
**Formalization Solution:** Every assumption must be explicit

### Pitfall 2: Subtle Identity Issues
**Problem:** Higher categorical identities are complex (Simpson-Kapranov-Voevodsky case)
**Formalization Solution:** Computer checks all identity conditions rigorously

### Pitfall 3: Sketched Definitions
**Problem:** Definitions given informally, not fully specified
**Formalization Solution:** Axiomatic approach (Strategy 2) or synthetic (Strategy 3)

### Pitfall 4: Scale of Work
**Problem:** Theorems depend on dozens of lemmas, hard to verify manually
**Formalization Solution:** Computer checks all dependencies

### Pitfall 5: Coherence Conditions
**Problem:** Higher categories require compatibility across many levels
**Formalization Solution:** Type system enforces coherence automatically

---

## VIII. INTEGRATION WITH OTHER FIELDS

### Music & Topos Theory (Your "music-topos" project?)

**Connection Points:**
- Categories for music theory structure
- Topoi for modeling modal/tonal spaces
- Generalized elements for representing harmonic elements
- Higher categories for temporal/polyrhythmic relations

**Formalization Potential:**
- Define musical categories axiomatically
- Prove theorems about harmonic relationships
- Use synthetic type theory for natural musical reasoning

### Classical Mechanics (Your "emmy-sicm" project?)

**Connection Points:**
- Categorical formulation of Lagrangian mechanics
- Fibrations for phase space structure
- Derived geometry for constraint spaces
- Infinity categories for histories/paths

**Formalization Potential:**
- Formalize symplectic geometry
- Prove conservation laws categorically
- Verify energy/momentum structure preservation

---

## IX. ECONOMICS OF FORMALIZATION

### Key Insight (from Riehl's talk)

This is fundamentally an **economics question**, not just correctness:

**Current System:**
- Famous mathematicians (Voevodsky, Tao, Lurie) can publish post-rigorous work that gets credited as "proof"
- Others cannot get equivalent credit for sketches
- Sociological advantage of reputation

**Formalization Future:**
- Clear separation: sketch vs. complete proof
- Credit flows to person who fills gaps
- More equitable attribution
- Historical example: Grothendieck papers → master's theses (took years to rigorize)

### Cost-Benefit Analysis

**Strategy 1 (Concrete Model):**
- Cost: High (full formalization effort)
- Benefit: One model fully formalized
- ROI: Medium (useful but not generalizable)

**Strategy 2 (Axioms):**
- Cost: Very high (axiomatization + prove models exist)
- Benefit: All theorems work for all models
- ROI: Exceptional (one proof, infinite models)

**Strategy 3 (Synthetic):**
- Cost: High (learn new proof assistant, develop theory)
- Benefit: Natural presentation, perfect alignment
- ROI: High (if domain is fixed, not generalizable)

---

## X. NEXT STEPS & RESOURCES

### To Learn More

**On Post-Rigorous Mathematics:**
1. Find Terry Tao's blog post on three stages
2. Read Voevodsky's essay on proof assistance motivation
3. Study Riehl's talk transcript (you have this)

**To Start Formalizing:**
1. **Strategy 1:** Learn Lean, work through mathlib tutorials
2. **Strategy 2:** Study Riehl & Verity "Elements of ∞-Category Theory", attempt to formalize definitions
3. **Strategy 3:** Learn Rzk, follow Riehl's formalization work

**To Understand Better:**
1. Read Lurie's "Higher Topos Theory" (if pursuing infinity categories)
2. Study Simpson's counterexample paper (understand failure modes)
3. Review Gaitsgory-Rozenblyum (model for gap-marking)

### Community Resources

- **arXiv:** Search "formalization", "infinity category", "proof assistant"
- **MathOverflow:** Ask specific formalization questions
- **Lean Zulip:** Active community discussion
- **Rzk GitHub:** Ongoing development and examples

---

## XI. SUMMARY TABLE

| Strategy | Tool | Cost | Benefit | Best For |
|----------|------|------|---------|----------|
| 1. Concrete | Lean/Coq | Very High | Single model | Practical applications |
| 2. Axioms | Lean/Coq | Extreme | Unlimited models | Foundational work |
| 3. Synthetic | Rzk | High | Natural alignment | Domain-specific theory |

---

## XII. BIBLIOGRAPHY STYLE REFERENCES

Baez, J. C., & Dolan, J. (1990s). The Cobordism Hypothesis. Unpublished conjecture.

Gaitsgory, D., & Rozenblyum, N. (2022). Derived Algebraic Geometry. American Mathematical Society. (Two volumes, 1000+ pages)

Kapranov, M., & Voevodsky, V. (1991). Infinity groupoids and homotopy types. *Cahiers de Topologie et Géométrie Différentielle Catégoriques*, 32(1).

Lurie, J. (2009). *Higher Topos Theory*. Princeton University Press.

Riehl, E., & Verity, D. (2022). *Elements of ∞-Category Theory*. Cambridge University Press.

Simpson, C. (1998). Calculating the 3-type of S² [Preprint]. arXiv. (Contradicts Kapranov-Voevodsky)

Tao, T. (Date unknown). "The Three Stages of Mathematical Education." Terry Tao's Blog. (Source of post-rigorous framework)

Voevodsky, V. (2014). "What If Current Foundations of Mathematics Are Inconsistent?" (Essay on motivations for formal verification)

---

## XIII. QUESTIONS FOR FURTHER EXPLORATION

1. **Bridging informality and formality:** How can we make formalization feel natural to working mathematicians?
2. **Economics of rigor:** What's the minimal cost to formalize a given mathematical domain?
3. **Sketch proofs:** Can we have a formal category of "formalized blueprints" with marked gaps?
4. **Credit attribution:** How should credit be distributed for proof + formalization?
5. **Domain specialization:** Should we build more specialized proof assistants like Rzk?
6. **Foundational choices:** Can we formalize across multiple foundations (ZFC, HoTT, cubical type theory)?
7. **Integration with other fields:** How can formalization of pure mathematics accelerate applied work (your music, mechanics projects)?

