# Formalizing Post-Rigorous Mathematics: Complete Guide Index

## Overview

This is a comprehensive resource package for understanding, planning, and implementing formalization of mathematical theories—drawn from Emily Riehl's 2024 talk at the Hausdorff Center for Mathematics on "Formalizing Post-Rigorous Mathematics."

The package contains:
1. **Deep analysis** of post-rigorous mathematics concept and formalization approaches
2. **Complete resource guide** with references, tools, and case studies
3. **Practical decision tree** for choosing formalization strategy
4. **This index** to navigate the material

---

## Quick Start (5 minutes)

**New to formalization?**
1. Read the "Core Concept" section below
2. Jump to **formalization-decision-tree.md** Section I (Quick Decision Tree)
3. Follow the tree to find your strategy

**Interested in the theory?**
1. Read through **riehl-post-rigorous-analysis.md** (comprehensive)
2. Review Section II (four case studies)
3. Study Section III (three formalization strategies)

**Looking for specific references?**
1. Go to **formalization-resources.md**
2. Find section you need (tools, people, concepts, etc.)
3. Use bibliography for full citations

---

## Document Map

### Document 1: riehl-post-rigorous-analysis.md (THEORY)

**Length:** ~3000 words
**Purpose:** Complete analysis of Riehl's talk
**Best for:** Understanding concepts deeply

**Key Sections:**
- I: Core concept (Tao's three stages + Riehl's redefinition)
- II: Four case studies from infinity category theory
- III: Three formalization strategies in detail
- IV: Economics of rigor (key insight)
- V: Case study with concrete example
- VI: Implications and tensions
- VII: References and concepts
- VIII: Open questions
- IX: Synthesis

**When to read:**
- Building conceptual foundation
- Writing about formalization
- Teaching others about post-rigorous math
- Understanding trade-offs between strategies

**Key takeaway:**
Post-rigorous mathematics is common and useful, but formalization makes the boundary between sketch and proof clear, and can democratize credit attribution.

---

### Document 2: formalization-resources.md (REFERENCE)

**Length:** ~5000 words
**Purpose:** Complete resource compilation
**Best for:** Finding information quickly

**Key Sections:**
- I: Foundational references (papers, people, institutions)
- II: Key figures and organizations
- III: Proof assistants (Lean, Rzk, Coq)
- IV: Formalization frameworks (strategies explained)
- V: Core mathematical concepts to formalize
- VI: Case studies for formalization
- VII: Common pitfalls and solutions
- VIII: Integration with other fields (music, mechanics)
- IX: Economics of formalization
- X: Next steps
- XI: Summary table
- XII: Bibliography
- XIII: Open questions for exploration

**When to use:**
- Looking up a specific paper or person
- Checking status of a proof assistant
- Finding examples to work through
- Understanding integration possibilities
- Building bibliography for your work

**Key resource:**
Section III (Proof Assistants) has current information on Lean 4, Rzk, and Coq.

---

### Document 3: formalization-decision-tree.md (PRACTICAL)

**Length:** ~4000 words
**Purpose:** Help choose and plan formalization approach
**Best for:** Decision-making and implementation planning

**Key Sections:**
- I: Quick decision tree (flowchart format)
- II: Detailed decision criteria (5 dimensions)
- III: Strategy-specific roadmaps (with timelines)
- IV: Concrete examples (worked through)
- V: Risk assessment (per strategy)
- VI: Hybrid approaches
- VII: Quick reference table
- VIII: Next steps checklist

**When to use:**
- Deciding which strategy to pursue
- Planning project timeline
- Understanding risks
- Comparing strategies side-by-side
- Building project roadmap

**Key reference:**
Section III (Strategy-Specific Roadmaps) has month-by-month plans.

---

### Document 4: FORMALIZATION-GUIDE-INDEX.md (THIS DOCUMENT)

**Purpose:** Navigation and context
**Best for:** Getting oriented, explaining to others

---

## The Three Strategies At a Glance

### Strategy 1: Concrete Model in Set Theory
**Tools:** Lean + Mathlib, Coq
**Timeline:** 3-24 months (scope-dependent)
**Cost:** High
**Benefit:** Working formalization of specific model
**When:** Single model, practical application, need community support

```
Mathematical example: Formalize quasi-categories fully
Time estimate: 12-18 months
Result: Everything about quasi-categories proven formally
Reuse: Only for quasi-categories
```

---

### Strategy 2: Infinity Cosmos (Axiomatic)
**Tools:** Lean + Mathlib, Coq
**Timeline:** 6-36 months (scales with model count)
**Cost:** Very high initially, then diminishing
**Benefit:** Theorems work across infinite models
**When:** Multiple models, want maximum generality, can invest in axiomatization

```
Mathematical example: Axiomatize Infinity Cosmos, prove two models
Time estimate: 20-24 months
Result: All theorems work for quasi-categories AND complete Segal spaces
Reuse: Each new model adds 1-2 months
Break-even: After 2-3 models
```

---

### Strategy 3: Synthetic Type Theory
**Tools:** Rzk (specialized)
**Timeline:** 4-18 months (scope-dependent)
**Cost:** High, but different (learning curve, ecosystem)
**Benefit:** Natural, elegant proofs that mirror mathematical intuition
**When:** Domain-specific, presentation matters, cutting-edge acceptable

```
Mathematical example: Formalize stable ∞-categories synthetically
Time estimate: 7 months
Result: Element-wise proofs are rigorous by design, very readable
Reuse: Only within Rzk (domain-specific) but provides blueprint
```

---

## Decision Checklist

Answer these questions to choose your strategy:

- [ ] **Scope:** Single theorem (1)? Whole theory (2-3)? Field (2-3)?
- [ ] **Models:** One (1)? Few (1-2)? Many (2)?
- [ ] **Timeline:** 3-6 mo (1-3)? 6-18 mo (any)? 18+ mo (2)?
- [ ] **Community:** Need help (1)? Solo OK (3)? Bleeding edge OK (3)?
- [ ] **Reuse:** For others (2)? For own work (1-3)? Exploratory (3)?

**Scoring:** Count strategy numbers above
- Majority 1? → **Use STRATEGY 1**
- Majority 2? → **Use STRATEGY 2**
- Majority 3? → **Use STRATEGY 3**

See **formalization-decision-tree.md** for detailed explanation.

---

## Core Concepts

### Post-Rigorous Mathematics
Arguments that are:
- Not explained in full detail
- Contain claims that "might not quite be true as stated"
- Are "morally correct" or "globally true" despite local errors
- Have errors that propagate but cancel out later

This is normal in mathematical literature, not a failure. But formalization makes the boundary clear.

### Three Stages of Mathematical Development (Tao)
1. **Pre-rigorous:** Informal, intuitive, computation-focused (early undergrad)
2. **Rigorous:** Formal, abstract, theory-focused (grad school)
3. **Post-rigorous:** Comfortable with rigor, revisits intuition with formal backing (expert level)

Post-rigorous is aspirational in Tao's framework, but practical in Riehl's.

### The Economics Insight
This is fundamentally an economics question:
- **Current:** Famous mathematicians can publish sketches that count as proofs
- **With formalization:** Clear separation between sketch and proof
- **Benefit:** Credit goes to person who formalizes, not original author
- **Effect:** More equitable attribution, clearer progress tracking

---

## Key Case Studies

### Case 1: Kapranov-Voevodsky (1991) vs Simpson (1998)
**Issue:** Contradiction discovered 15 years later, no obvious error
**Lesson:** Formal verification would catch subtle mistakes early
**Reference:** riehl-post-rigorous-analysis.md, Section II Case 1

### Case 2: Lurie's "On Infinity Topoi"
**Issue:** 100-page paper without precise definition of main object
**Lesson:** Community needs axiomatization, not just intuitive sketch
**Reference:** riehl-post-rigorous-analysis.md, Section II Case 2

### Case 3: Cobordism Hypothesis
**Issue:** "Proof" exists only as detailed sketch, status unclear
**Lesson:** Formalized blueprints could clarify what's proven vs. conjectural
**Reference:** riehl-post-rigorous-analysis.md, Section II Case 3

### Case 4: Gaitsgory-Rozenblyum (DAG)
**Issue:** 1000+ page work with 7 explicit unproven statements
**Lesson:** Transparent gap-marking is good; spawns productive research
**Reference:** riehl-post-rigorous-analysis.md, Section II Case 4

---

## Proof Assistants Comparison

| Tool | Best For | Maturity | Community | Learning Curve |
|------|----------|----------|-----------|-----------------|
| **Lean 4** | Strategy 1-2, practical | Mature | Large | Medium |
| **Coq** | Strategy 1-2, general | Mature | Medium | Medium |
| **Rzk** | Strategy 3, ∞-categories | Developing | Small | Hard |

**Current Status (2024):**
- **Lean 4:** Most mature, best for new projects
- **Mathlib:** Extensive library, 90K+ theorems formalized
- **Rzk:** Emily Riehl actively developing, specialized for infinity categories
- **Coq:** Solid, good for foundational work

**Reference:** formalization-resources.md, Section III

---

## Common Pitfalls & How Formalization Helps

| Pitfall | Problem | Formalization Solution |
|---------|---------|------------------------|
| Hidden assumptions | Readers must fill gaps | Every assumption explicit |
| Subtle identities | Identity conditions complex | Computer checks all |
| Sketched definitions | Definitions informal | Axiomatize or formalize precisely |
| Scale | 100s of lemmas hard to verify | Computer checks all dependencies |
| Coherence | Compatibility across levels | Type system enforces |

**Reference:** formalization-resources.md, Section VII

---

## Next Steps by Role

### If you're an **expert in a field**:
1. Read riehl-post-rigorous-analysis.md (understand landscape)
2. Use formalization-decision-tree.md (choose strategy)
3. Check formalization-resources.md for proof assistant status
4. Start with small, well-understood theorem as proof-of-concept

### If you're a **proof assistant developer**:
1. Read formalization-resources.md (understand proof assistant landscape)
2. Study Section IV (formalization frameworks) to see where your tool fits
3. Look at current Rzk/Lean formalization work for examples
4. Consider what community needs (axiomatization support, synthetic features, etc.)

### If you're a **mathematician curious about formalization**:
1. Start with riehl-post-rigorous-analysis.md (digestible overview)
2. Skim formalization-decision-tree.md Section II (decide if worth pursuing)
3. Watch Emily Riehl's 2024 talk (original source)
4. Try small formalization project as experiment

### If you're **planning a formalization project**:
1. Answer decision checklist above
2. Read formalization-decision-tree.md Section III for your strategy
3. Review formalization-resources.md for references and examples
4. Build detailed timeline using roadmaps in decision-tree.md

---

## How to Share This Material

### For a Talk/Presentation:
Use **riehl-post-rigorous-analysis.md** (Sections I-II) as outline
- 30 min version: Focus on case studies
- 60 min version: Add strategies + implications
- 90 min version: Include decision-making and planning

### For a Reading Group:
1. **Session 1:** Core concepts (riehl, Sections I)
2. **Session 2:** Case studies (riehl, Section II)
3. **Session 3:** Strategy deep-dive (riehl, Section III)
4. **Session 4:** Planning practical project (decision-tree, Section III)

### For a Team Planning Formalization:
1. Distribute formalization-decision-tree.md
2. Workshop: each person fills out decision checklist
3. Discuss: compare answers, reach consensus
4. Use Strategy Roadmap from decision-tree.md Section III

### For Publication/Repository:
All three documents are ready to:
- Include in GitHub repository
- Publish on blog/wiki
- Contribute to mathematical community resources
- Use as foundation for more specialized guides

---

## Updates & Maintenance

**These documents reflect:**
- Emily Riehl's talk (July 2024)
- Proof assistant status (late 2024)
- Current research direction (Rzk, infinity cosmos)

**May need updates when:**
- Rzk releases major version
- New proof of important theorem
- Significant shift in formalization practice
- New strategies or tools emerge

---

## Credits & Sources

**Primary Source:**
Emily Riehl: "Formalizing Post-Rigorous Mathematics"
Hausdorff Center for Mathematics, July 15, 2024
[Video + Transcript Available]

**Secondary Sources:**
- Terry Tao's Blog (three stages framework)
- Vladimir Voevodsky's Essays (motivation for formalization)
- Riehl & Verity: Elements of ∞-Category Theory (strategy 2)
- Rzk Documentation (strategy 3)
- Lean/Mathlib Documentation (strategy 1)

**Compilation & Organization:**
Created as comprehensive reference package for working mathematicians and formalization practitioners.

---

## Table of Contents: Full Material

### riehl-post-rigorous-analysis.md
- I. Core Concept
- II. Four Case Studies
- III. Three Strategies
- IV. Economics Question
- V. Case Study Details
- VI. Implications
- VII. References
- VIII. Open Questions
- IX. Synthesis

### formalization-resources.md
- I. Foundational References
- II. People & Institutions
- III. Proof Assistants
- IV. Formalization Frameworks
- V. Mathematical Concepts
- VI. Case Studies
- VII. Pitfalls & Solutions
- VIII. Integration with Other Fields
- IX. Economics
- X. Next Steps
- XI. Summary Table
- XII. Bibliography
- XIII. Questions

### formalization-decision-tree.md
- I. Quick Decision Tree
- II. Detailed Decision Criteria
- III. Strategy-Specific Roadmaps
- IV. Concrete Examples
- V. Risk Assessment
- VI. Hybrid Approaches
- VII. Quick Reference Table
- VIII. Next Steps

---

## Questions?

**About post-rigorous mathematics?**
→ See riehl-post-rigorous-analysis.md, Section I

**Choosing a strategy?**
→ See formalization-decision-tree.md, Section I

**Finding resources/papers?**
→ See formalization-resources.md, Section I-II

**Planning a project?**
→ See formalization-decision-tree.md, Section III-IV

**Understanding risks?**
→ See formalization-decision-tree.md, Section V

---

## Last Updated

December 26, 2025
Based on Emily Riehl's 2024 talk
Compiled as comprehensive reference guide

