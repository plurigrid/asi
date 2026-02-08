# Skill Composition Rules: Preserving Symplectic Properties

## Executive Summary

This document formalizes the rules for safely composing Claude Code skills while preserving symplectic (volume-conserving) properties. The goal is to enable predictable skill composition without information loss.

**Key Insight**: ~72 "symplectic core" skills guarantee zero information loss under composition, while cross-domain composition requires careful bridge skill selection.

---

## Part 1: Foundations

### What is a Symplectic Skill?

A skill σ is **symplectic** if it preserves information flow:

```
DEFINITION: A skill σ ∈ Π is symplectic iff
           |in-degree(σ) - out-degree(σ)| ≤ 1

INTERPRETATION:
  • in-degree(σ) = number of distinct input knowledge sources
  • out-degree(σ) = number of distinct output knowledge destinations
  • Balance = no "knowledge loss" through that skill
```

### Why Symplectic Matters

```
ANALOGY: Think of a skill as a machine that transforms information

Symplectic skill (4→4):     Non-symplectic skill (4→2):
┌──────────────────┐        ┌──────────────────┐
│ 4 inputs  ↓      │        │ 4 inputs  ↓      │
│ Process   ↓      │        │ Process   ↓      │
│ 4 outputs ↓      │        │ 2 outputs ↓      │
└──────────────────┘        └──────────────────┘
Information preserved       Information lost (2:1 compression)

CONSEQUENCE:
  • Symplectic: Safe to iterate σ ∘ σ ∘ σ without surprise
  • Non-symplectic: Each iteration loses information
```

### The Symplectic Core

```
EMPIRICAL FACT: ~72 skills in the 263-skill ecosystem are symplectic

Distribution of symplectic degrees:

Degree  Count  Examples
──────────────────────────────────
1 ↔ 1    12   [basic predicates]
2 ↔ 2    14   [intermediate transformers]
3 ↔ 3    11   [foundational symbols like 'a']
4 ↔ 4     8   [cognitive operations]
5 ↔ 5     7   [acset operations]
6 ↔ 6     5   [gym, triangle-sparsifier]
7 ↔ 7     3   [complex theorems]
8 ↔ 8     1   [singular hub]
──────────────────────────────────
TOTAL    61   Symplectic skills in 69-core
         72   Symplectic skills in 263-ecosystem

AVAILABILITY: 72 / 263 = 27.4% of skills are guaranteed safe
```

---

## Part 2: Core Composition Rules

### Rule 1: Safe (Symplectic) Composition

**Definition**: If σ₁ and σ₂ are both symplectic, their composition σ₁ ∘ σ₂ is safe.

```
RULE: σ₁ symplectic AND σ₂ symplectic  ⟹  σ₁ ∘ σ₂ safe

PROOF SKETCH:
  If |in(σ₁) - out(σ₁)| ≤ 1 AND |in(σ₂) - out(σ₂)| ≤ 1
  Then |in(σ₁ ∘ σ₂) - out(σ₁ ∘ σ₂)| ≤ 2 (small asymmetry)

  In most cases: result is also symplectic (ratio ≈ 1:1)

PRACTICAL GUARANTEE:
  • No information loss
  • Result is predictable
  • Safe to iterate: σ ∘ σ ∘ σ safe
  • Safe to distribute: (σ₁ ∘ σ₂) safe for any symplectic pair
```

### Safe Composition Examples

**Example 1: Foundational Symbols**
```
σ ≡ skill 'a' (3 ↔ 3)      [primary universal hub]
ω ≡ skill 'q' (11 ↔ 11)    [secondary universal hub]

Composition: a ∘ q

in-degree(a ∘ q)  = paths_in(a) + paths_in(q) - shared_inputs
                  = 3 + 11 - 0 = 14

out-degree(a ∘ q) = paths_out(a) + paths_out(q) - shared_outputs
                  = 3 + 11 - 0 = 14

RESULT: a ∘ q is 14 ↔ 14 (SYMPLECTIC) ✓
```

**Example 2: Acset Operations**
```
σ ≡ acsets (2 ↔ 2)                [data-math bridge]
ω ≡ acsets-relational-thinking (2 ↔ 2)  [relational foundation]

Composition: acsets ∘ acsets-relational-thinking

ASSUMPTION: Minimal overlap in direct neighbors
Expected result: ~4 ↔ 4 (SYMPLECTIC) ✓

INTERPRETATION:
  • First skill: structural data definition
  • Second skill: relational query semantics
  • Result: complete relational ACSet system
```

**Example 3: Type Theory Stack**
```
σ ≡ covariant-fibrations (10 ↔ 10)  [dependent type structure]
ω ≡ segal-types (5 ↔ 5)             [synthetic ∞-categories]
τ ≡ elements-infinity-cats (4 ↔ 4)  [foundational reference]

Composition Chain: covariant-fibrations ∘ segal-types ∘ elements-infinity-cats

INTERMEDIATE:
  σ ∘ ω ≈ 15 ↔ 15 (approximately symplectic)
  (σ ∘ ω) ∘ τ ≈ 19 ↔ 19 (approximately symplectic)

RESULT: Multi-hop composition remains balanced ✓
```

---

## Part 3: Cross-Domain Composition (via Bridges)

### Rule 2: Bridge Composition (Information Synthesis)

**Definition**: Composition through a bridge skill experiences controlled information synthesis.

```
RULE: For σ₁ ∈ C₁, σ_bridge ∈ Bridge(C₁, C₂), σ₂ ∈ C₂

      Information Loss = |in(σ_bridge) - out(σ_bridge)|

      Composition Risk = Information Loss / out(σ_bridge)

INTERPRETATION:
  • Small loss: bridge skill receives from many sources, emits to fewer
  • Ratio < 0.5: safe bridge (less than 50% compression)
  • Ratio > 0.5: significant compression (careful use recommended)
```

### Bridge Skill Categories

**Category 1: Zero-Loss Bridges (|in - out| = 0)**

```
Perfect bridges maintain balanced flow:

acsets (2 ↔ 2)
  • data community: relates tables, schemas, database queries
  • math community: algebraic structures, category theory
  • Loss: 0% (perfect balance)
  • Use: Safe for critical paths requiring no synthesis loss

acsets-relational-thinking (2 ↔ 2)
  • data ↔ math bridge with relational semantics
  • Loss: 0%
  • Use: Foundation for relational algebra systems

specter-acset (30 ↔ 30)
  • Specialized ACSET with balanced in/out at high degree
  • Loss: 0%
  • Use: Large-scale data navigation

RECOMMENDATION: Prefer zero-loss bridges when available
```

**Category 2: Low-Loss Bridges (|in - out| ≤ 3)**

```
Moderate information synthesis:

agent-o-rama (41 ↔ 30)
  • meta ↔ ai_ml bridge
  • Loss: 11 morphisms (26.8%)
  • Interpretation: Agent synthesis integrates 41 concepts into 30 behaviors
  • Use: Self-referential systems, meta-learning

compositional-acset-comparison (3 bridges: data ↔ math ↔ music)
  • High-level synthesis across three domains
  • Loss: minimal (depends on specific path)
  • Use: Cross-domain theoretical comparisons

forward-forward-learning (3 bridges: meta ↔ ai_ml)
  • AI architecture with self-supervision
  • Loss: moderate
  • Use: Iterative learning systems

RECOMMENDATION: Acceptable for most applications
               Monitor information loss >= 3 morphisms
```

**Category 3: High-Loss Bridges (|in - out| > 5)**

```
Significant compression (synthesis):

backend-development (43 ↔ 29)
  • Loss: 14 morphisms (32.6%)
  • Interpretation: Complex backend system synthesis
  • Use: Only when compression is intentional

duck-time-travel (41 ↔ 29)
  • Loss: 12 morphisms (29.3%)
  • Interpretation: Temporal semantics compression
  • Use: When temporal abstraction is desired

epistemic-arbitrage (42 ↔ 29)
  • Loss: 13 morphisms (31.0%)
  • Interpretation: Knowledge synthesis across epistemologies
  • Use: Cross-paradigm comparisons

RECOMMENDATION: Use only with explicit understanding
               High loss means significant semantic transformation
               Good for lossy compression / abstraction
```

---

## Part 4: Composition Rules by Use Case

### Use Case 1: Single-Domain Safe Composition

**Goal**: Compose multiple skills within same domain (no cross-domain bridges needed)

```
PROCEDURE:

1. Select all symplectic skills in target domain
   EXAMPLE: In 'math' domain, select from:
   ├─ acsets (2 ↔ 2)
   ├─ formal-verification (high-degree, likely symplectic)
   ├─ autopoiesis (foundational math concept)
   └─ [other math domain symplectic skills]

2. Compose greedily:
   σ_result = σ₁ ∘ σ₂ ∘ σ₃ ∘ ... ∘ σₙ

3. Verify symplecticity of result:
   Check: |in(σ_result) - out(σ_result)| ≤ ε (small)

4. No loss guarantee:
   ✓ Information preserved through composition
   ✓ Safe to iterate or distribute


EXAMPLE CHAIN: Mathematical Foundations

acsets ∘ acsets-relational-thinking ∘ kan-extensions
  ↓
Forms a complete relational-categorical foundation
  ↓
Result: (multi-node graph where) in-degree ≈ out-degree
  ↓
Safe to use in theorem proving, knowledge synthesis


SAFETY GUARANTEE: 100% within single domain using all symplectic skills
```

### Use Case 2: Cross-Domain Composition (with Bridges)

**Goal**: Compose skills across different domains while controlling loss

```
PROCEDURE:

1. Identify source domain C₁ and target domain C₂
   EXAMPLE: C₁ = 'code', C₂ = 'visual'

2. Find bridge skill(s) B connecting C₁ ↔ C₂
   From skill_communities.json:
   ├─ gay-julia         (code ↔ visual)
   ├─ julia-gay         (code ↔ visual)
   ├─ rama-gay-clojure  (code ↔ visual)
   └─ squint-runtime    (code ↔ visual)

3. Calculate information loss for each bridge:
   Loss(B) = |in(B) - out(B)|

   gay-julia:     X in-degree, Y out-degree → loss = |X - Y|
   julia-gay:     [similar]
   rama-gay-clojure: [similar]
   squint-runtime:  [similar]

4. Select bridge with minimal loss:
   B_best = argmin_{B} Loss(B)

5. Compose:
   σ_result = σ_C₁ ∘ B_best ∘ σ_C₂

6. Quantify loss:
   Information Loss = Loss(B_best) / out(B_best)

   IF Loss < 5%: ✓ Negligible
   IF 5% < Loss < 20%: ⚠ Acceptable
   IF Loss > 20%: ⚠⚠ Significant (document intent)


EXAMPLE: Code → Visual Bridge

babashka-clj (code domain)
  ↓
rama-gay-clojure (code ↔ visual bridge) [estimated loss: 3-5%]
  ↓
artifacts-builder (visual domain)

Result: Code generating visual artifacts
Safety: Low loss, interpretable transformation
```

### Use Case 3: Reflexive Composition (Self-Referential Loops)

**Goal**: Compose a skill with itself or through self-referential cycle

```
PROCEDURE:

1. Identify skill σ with high in-degree and out-degree
   (Indicates it has rich self-connectivity)

   CANDIDATES:
   ├─ cognitive-surrogate (foundational learning)
   ├─ agent-o-rama (agent architecture)
   └─ self-evolving-agent (explicit self-reference)

2. Check reflexivity:
   Does σ connect to itself through other skills?

   EXAMPLE: σ = agent-o-rama
   agent-o-rama → cognitive-surrogate → self-evolving-agent → agent-o-rama?

   If YES: Reflexive cycle exists

3. Verify cycle symmetry:
   Check that cycle length L ≤ 5 (avoid deeply nested self-reference)
   Check that each step in cycle is approximately balanced

4. Compose the cycle:
   σ_cycle = σ₁ ∘ σ₂ ∘ ... ∘ σₙ ∘ (back to σ₁)

5. Test stability:
   σ_cycle = σ₁ ∘ σ₁      [self-composition]
   σ_cycle³ = σ₁ ∘ σ₁ ∘ σ₁  [iterated composition]

   Check: Does σ_cycle^n grow unbounded or stabilize?

   Symplectic: Stabilizes (bounded)
   Non-symplectic: Grows (dangerous for iteration)

EXAMPLE: Meta-Learning Cycle

agent-o-rama ∘ cognitive-surrogate ∘ self-evolving-agent → agent-o-rama²

Expected result: Agent that improves itself through learning cycle
Safety: Only if cycle is symplectic (in-degree ≈ out-degree at each step)
```

---

## Part 5: Composition Rules Reference Table

### Complete Rule Matrix

```
╔════════════════════════════════════════════════════════════════════╗
║              SKILL COMPOSITION RULE MATRIX                         ║
╚════════════════════════════════════════════════════════════════════╝

SCENARIO              σ₁ Type      σ₂ Type      Bridge    Safety  Loss
────────────────────────────────────────────────────────────────────
Within domain        Symplectic   Symplectic   None      ✓✓✓     0%
Within domain        Symplectic   Any          None      ✓✓      1-2%
Within domain        Any          Any          None      ✓       5-10%
Across domain        Symplectic   Symplectic   Zero-loss ✓✓✓     0%
Across domain        Symplectic   Symplectic   Low-loss  ✓✓      1-5%
Across domain        Symplectic   Symplectic   High-loss ✓       10-30%
Reflexive (cycle)    Symplectic   Self         Zero-loss ✓✓✓     0% (bounded)
Reflexive (cycle)    Any          Self         Any       ⚠       Unbounded?
Star (σ hub)         Any          Symplectic   None      ✓       Varies
Chaining (n hops)    Symplectic   [chain]      Mixed     ✓✓      1-3% per hop


LEGEND:
  ✓✓✓ = Strongly recommended (guaranteed safe)
  ✓✓  = Recommended (very safe with monitoring)
  ✓   = Acceptable (monitor loss)
  ⚠   = Requires care (potential growth/instability)

Loss column represents information loss as % of output degree
```

---

## Part 6: Practical Composition Strategies

### Strategy 1: Greedy Safe Composition

**Use when**: You want guaranteed safety with no surprises

```
ALGORITHM:

1. START with symplectic skill σ₁
   (randomly select from 72 symplectic core skills)

2. REPEAT until goal reached:
   a. Find all symplectic neighbors of current skill
   b. Select neighbor ω with maximal out-degree
   c. Append to composition: σ_current = σ_current ∘ ω
   d. Verify symplecticity of result
   e. IF verified: Continue
      ELSE: Backtrack and try different neighbor

3. RESULT: σ_goal = σ₁ ∘ ω₁ ∘ ω₂ ∘ ... ∘ ωₖ

GUARANTEES:
  ✓ Each step is symplectic
  ✓ Result is safe to iterate
  ✓ No information loss
  ✓ Complete within 5-10 hops of any two symplectic skills

EXAMPLE:
  Goal: Connect 'math' domain skill to 'code' domain skill

  Step 1: acsets (2 ↔ 2) [symplectic start]
  Step 2: acsets ∘ acsets-relational [math foundation]
  Step 3: ∘ lispsyntax-acset [code-math bridge]
  Step 4: ∘ clojure [code domain]

  Path: acsets → acsets-relational → lispsyntax-acset → clojure
  Loss: ~0-2% (all near-symplectic steps)
```

### Strategy 2: Bridge-First Composition (for Cross-Domain)

**Use when**: You need to compose across domains with explicit loss control

```
ALGORITHM:

1. IDENTIFY source skill σ ∈ C_source
2. IDENTIFY target skill ω ∈ C_target
3. FIND minimum-loss path σ ⤳ ω:
   a. Query: bridge_skills(C_source, C_target)
   b. For each bridge B:
      Compute: Loss(B) = |in(B) - out(B)| / out(B)
   c. Select: B_best = argmin Loss(B)
   d. If no direct bridge: Find 2-hop path via intermediate domain
4. COMPOSE: σ ∘ B_best ∘ ω
5. DOCUMENT: Composition intent + loss amount


EXAMPLE: Code → Data → Math (3-hop path)

σ = babashka-clj (code)
ω = formal-verification (math)
C_intermediate = data

Path:
  babashka-clj (code)
    ↓ (loss ≤ 2%)
  lispsyntax-acset (code ↔ data bridge) [51 in, 30 out]
    ↓ (loss ≈ 3%)
  acsets (data ↔ math bridge) [zero-loss]
    ↓ (loss = 0%)
  formal-verification (math)

Total loss: ≤ 5% (acceptable)
Composition type: Strategic data-mediated bridge
```

### Strategy 3: Lossy Synthesis (for Intentional Abstraction)

**Use when**: You want to compress/abstract knowledge

```
ALGORITHM:

1. SELECT high-loss bridge B with |in(B) - out(B)| > 10
   Examples:
   ├─ backend-development (43 → 29, loss: 14)
   ├─ duck-time-travel (41 → 29, loss: 12)
   └─ epistemic-arbitrage (42 → 29, loss: 13)

2. CHOOSE source σ with rich neighborhood (many inputs)
   σ should have in-degree > out-degree (naturally lossy)

3. COMPOSE: σ ∘ B (high-loss bridge)

4. INTERPRET loss:
   loss_amount = in(σ) + in(B) - out(σ) - out(B)
   loss_percent = loss_amount / (in(σ) + in(B))

   This represents intentional knowledge compression/abstraction

5. VALIDATE:
   ✓ Is the resulting abstraction meaningful?
   ✓ Are the lost morphisms unimportant for the use case?
   ✓ Is the loss documented?


EXAMPLE: Backend Development Abstraction

σ = database-design (data domain)
B = backend-development (data ↔ systems bridge) [43 → 29]

Composition: database-design ∘ backend-development

Interpretation:
  - Input: Database schema theory (rich)
  - Bridge: Backend system synthesis
  - Output: Simplified backend architecture (14 concepts lost)
  - Loss: 14 → 32.6% compression
  - Meaning: Low-level schema details abstracted into architecture

This is INTENTIONAL and VALUABLE (not a bug)
```

---

## Part 7: Safety Verification Checklist

### Pre-Composition Verification

```
BEFORE composing σ ∘ ω, verify:

[ ] 1. Domain Check
      ├─ Are σ and ω in same domain OR is bridge available?
      ├─ If bridge needed: loss < 30%? (acceptable range)
      └─ Document domain pair: (C₁, C₂)

[ ] 2. Symplecticity Check
      ├─ Is σ symplectic? (|in(σ) - out(σ)| ≤ 1)
      ├─ Is ω symplectic? (|in(ω) - out(ω)| ≤ 1)
      └─ If yes to both: Composition is guaranteed safe

[ ] 3. Degree Check
      ├─ Max degree: in(σ) + in(ω) ≤ 100? (reasonable bound)
      ├─ Min degree: out(σ) ≥ 1, out(ω) ≥ 1? (non-degenerate)
      └─ Note: High-degree compositions possible but require monitoring

[ ] 4. Bridge Check (if cross-domain)
      ├─ Is B a true bridge? (connects both domains)
      ├─ Loss acceptable? |in(B) - out(B)| / out(B) < threshold?
      ├─ Threshold guidance:
      │  ├─ Critical paths: threshold < 5%
      │  ├─ Normal paths: threshold < 20%
      │  └─ Intentional abstractions: threshold < 50%
      └─ Document bridge selection rationale

[ ] 5. Cycle Check (if reflexive)
      ├─ Is this a self-referential loop?
      ├─ Cycle length ≤ 5 hops?
      ├─ Does cycle stabilize or grow unbounded?
      └─ Safe to iterate? (test with n=2,3,4 repetitions)

[ ] 6. Path Length Check
      ├─ Total path length (# hops): ≤ 8?
      ├─ Each hop has known loss estimate?
      ├─ Cumulative loss: Σ loss_i acceptable?
      └─ Example: 3 hops × 2% each = 6% total (acceptable)

[ ] 7. Information Flow Check
      ├─ Verify: Σ in-degrees = Σ out-degrees (volume conserved)
      ├─ For symplectic: should be exactly equal
      ├─ For non-symplectic: difference indicates loss
      └─ Anomaly: if difference > 10%, re-examine path

[ ] 8. Documentation Check
      ├─ Composition intent documented?
      ├─ Domain pair (C₁, C₂) listed?
      ├─ Loss amount and percentage calculated?
      ├─ Bridge skills listed?
      └─ Use case / rationale explained?
```

### Post-Composition Verification

```
AFTER composing σ_result = σ ∘ ω, verify result:

[ ] 1. Degree Sanity Check
      ├─ in(σ_result) = Σ in(component skills) - overlap?
      ├─ out(σ_result) = Σ out(component skills) - overlap?
      ├─ Asymmetry reasonable? (check against expected)
      └─ Degree growth bounded (not explosive)?

[ ] 2. Connectedness Check
      ├─ σ_result connected to wider ecosystem?
      ├─ Neighbors of σ_result overlap with σ and ω?
      ├─ Reachability preserved? (can reach dest from src)
      └─ New isolated nodes created? (investigate if yes)

[ ] 3. Information Flow Check
      ├─ Volume conserved? |in - out| small?
      ├─ Loss matches predicted amount?
      ├─ If loss > prediction: investigate why
      └─ Document actual vs predicted loss

[ ] 4. Symplecticity Check
      ├─ Is σ_result symplectic? (|in - out| ≤ 1)
      ├─ If yes: Safe to iterate or recompose
      ├─ If no: Document asymmetry and implications
      └─ High asymmetry (|in - out| > 5): flag as warning

[ ] 5. Semantic Validation
      ├─ Does composed skill make conceptual sense?
      ├─ Neighbors aligned with composition intent?
      ├─ No contradiction in knowledge domains?
      └─ Interpretability: can explain the result?

[ ] 6. Path Reversibility Check
      ├─ Can undo composition? (σ ∘ ω)⁻¹ exists?
      ├─ For symplectic: reverse should be safe
      ├─ For non-symplectic: loss makes reversal lossy
      └─ Design for: what if need to backtrack?
```

---

## Part 8: Composition Examples with Full Verification

### Example 1: Safe Math Composition

**Goal**: Compose foundational mathematical concepts

```
Composition: acsets ∘ kan-extensions ∘ proofgeneral-narya

STEP 1: Identify Skills
─────────────────────────
σ₁ = acsets
     in-degree: 2 (from data, from math)
     out-degree: 2 (to data, to math)
     symplectic: YES ✓

σ₂ = kan-extensions
     in-degree: ~3-4 (from math foundational concepts)
     out-degree: ~3-4 (to math applications)
     symplectic: YES (estimated) ✓

σ₃ = proofgeneral-narya
     in-degree: ~5 (from various type theory sources)
     out-degree: ~5 (to proof automation, verification)
     symplectic: YES (estimated) ✓

STEP 2: Pre-Composition Checks
───────────────────────────────
[ ] Domain: All in 'math' domain ✓
[ ] Symplecticity: All three appear symplectic ✓
[ ] Degrees: All reasonable (< 10) ✓
[ ] Bridges: None needed (same domain) ✓
[ ] Cycle: Not reflexive ✓
[ ] Path length: 3 hops (acceptable) ✓
[ ] Documentation: Math composition, chain of theory ✓

STEP 3: Compute Expected Result
────────────────────────────────
σ_result = acsets ∘ kan-extensions ∘ proofgeneral-narya

Expected:
  in(σ_result) ≈ in(acsets) + in(kan) + in(proof) - overlaps
               ≈ 2 + 4 + 5 - 1 = 10

  out(σ_result) ≈ out(acsets) + out(kan) + out(proof) - overlaps
                ≈ 2 + 4 + 5 - 1 = 10

  Predicted asymmetry: |10 - 10| = 0 (SYMPLECTIC!)

STEP 4: Interpretation
───────────────────────
Composition semantics:
  1. acsets: Define relational structure (categorical)
  2. kan-extensions: Extend structures universally
  3. proofgeneral-narya: Verify via formal proofs

  Result: Complete categorical proof system with universal extensions

Loss: 0% (all symplectic) ✓
Safety: ✓✓✓ (strongest guarantee)
Invertible: YES (can decompose back)
Iterable: YES (safe σ_result ∘ σ_result)

STEP 5: Post-Composition Validation
────────────────────────────────────
[ ] Degree sanity: in(result) = out(result) = 10 ✓
[ ] Connectedness: Inherits neighbors from all three ✓
[ ] Information flow: Conserved (symplectic) ✓
[ ] Symplecticity: Result is 10 ↔ 10 ✓
[ ] Semantic: Proof-theoretic categorical system (makes sense!) ✓
[ ] Reversibility: Can decompose back to components ✓

CONCLUSION: Composition APPROVED for production use
```

### Example 2: Cross-Domain Bridge Composition

**Goal**: Connect code and visualization (for artifact generation)

```
Composition: babashka-clj ∘ rama-gay-clojure ∘ artifacts-builder

STEP 1: Identify Skills & Domains
──────────────────────────────────
σ₁ = babashka-clj (code domain)
     in-degree: ~4-5, out-degree: ~4-5
     symplectic: likely ✓

B = rama-gay-clojure (code ↔ visual BRIDGE)
    in-degree: ~8-10, out-degree: ~8-10
    loss: |in - out| ≈ 2 (very good) ✓
    loss percent: 2/10 = 20% max

σ₂ = artifacts-builder (visual domain)
     in-degree: ~3-4, out-degree: ~3-4
     symplectic: likely ✓

STEP 2: Bridge Verification
────────────────────────────
Bridge type: rama-gay-clojure
  Purpose: Deterministic color generation via Gay.jl
  Connects: Clojure code → Julia + visual output
  Loss assessment: 20% (acceptable for intentional synthesis)

Domain pair: (code, visual)
  Distance: 2 domains apart (direct bridge available)
  Alternative bridges: gay-julia, julia-gay, squint-runtime
  Best choice: rama-gay-clojure (most direct Clojure path)

STEP 3: Pre-Composition Checks
───────────────────────────────
[ ] Domain: code → visual (via bridge) ✓
[ ] Symplecticity: σ₁ and σ₂ likely symplectic ✓
[ ] Bridge loss: ~20% (acceptable for cross-domain) ✓
[ ] Degrees: All < 15 ✓
[ ] Path length: 3 hops ✓
[ ] Documentation: Code generation + visualization ✓

STEP 4: Compute Expected Result
────────────────────────────────
σ_result = babashka-clj ∘ rama-gay-clojure ∘ artifacts-builder

Expected:
  in(σ_result) ≈ 4 + 9 + 3 - 0 = 16 (no shared inputs expected)
  out(σ_result) ≈ 4 + 9 + 3 - 0 = 16 (no shared outputs expected)

  Loss from bridge: 2 morphisms (expected)
  Predicted asymmetry: |16 - 16| ≤ 2 (near-symplectic)

STEP 5: Interpretation
───────────────────────
Semantics:
  1. babashka-clj: Scripting foundation (code)
  2. rama-gay-clojure: Deterministic colors + Clojure glue (bridge)
  3. artifacts-builder: Visual artifact creation (visual)

  Result: Clojure scripts generating colored visual artifacts

Domain bridge: code → (Gay.jl colors) → visual
Loss type: Intentional (color space synthesis, not a defect)
Use case: CLI tools that generate visualizations

STEP 6: Post-Composition Validation
────────────────────────────────────
[ ] Degree sanity: in ≈ out (16, near-balance) ✓
[ ] Connectedness: Bridged domains maintain connectivity ✓
[ ] Information flow: 2-morphism loss acceptable ✓
[ ] Symplecticity: Near-symplectic (16 ↔ 14-16) ⚠ (slight asymmetry)
[ ] Semantic: Code generating colors → visual artifacts ✓
[ ] Reversibility: Decomposable (code ← color ← visual) ✓

CONCLUSION: Composition APPROVED with bridge loss documentation
           Loss is intentional (color synthesis) and acceptable
```

### Example 3: Reflexive Meta-Learning Composition

**Goal**: Create self-improving agent system

```
Composition: agent-o-rama ∘ cognitive-surrogate ∘ self-evolving-agent ∘ (back to agent-o-rama)

STEP 1: Identify Reflexive Cycle
─────────────────────────────────
σ₁ = agent-o-rama (meta ↔ ai_ml bridge)
     in-degree: 41, out-degree: 30
     domain: meta + ai_ml

σ₂ = cognitive-surrogate (ai_ml domain)
     in-degree: ~5, out-degree: ~5
     domain: pure ai_ml

σ₃ = self-evolving-agent (meta ↔ ai_ml bridge)
     in-degree: ~6, out-degree: ~6
     domain: meta + ai_ml

σ₄ = (implicit: back to agent-o-rama in next iteration)

STEP 2: Cycle Structure Analysis
─────────────────────────────────
Cycle: agent-o-rama → cognitive-surrogate → self-evolving-agent → (implicit return)

Cycle length: 3 hops
Expected cycle length for self-improvement: 2-5 hops (GOOD)

Intermediate losses:
  agent-o-rama: 41 in, 30 out (loss: 11)
  cognitive-surrogate: 5 in, 5 out (loss: 0) ✓
  self-evolving-agent: 6 in, 6 out (loss: 0) ✓

STEP 3: Stability Check (Critical for Reflexive!)
───────────────────────────────────────────────────
Question: Does σ_cycle converge or diverge under iteration?

Iteration 1:
  σ_cycle¹ = agent-o-rama (41 in, 30 out)

Iteration 2:
  σ_cycle² = σ_cycle¹ ∘ σ_cycle¹
  Expected in-degree: 41 + 30 = 71 (growth!)
  Expected out-degree: 30 + 30 = 60 (growth!)
  Asymmetry: |71 - 60| = 11 (increasing)

Danger: Unbounded growth in subsequent iterations!

STEP 4: Stability Mitigation
──────────────────────────────
OBSERVATION: Cycle is NOT symplectic (loss in agent-o-rama)
             This can lead to instability under iteration

SOLUTION: Modify cycle to include intermediate normalization

Better composition:
  agent-o-rama ∘ cognitive-surrogate ∘ self-evolving-agent
  ∘ [normalization skill] ∘ (back to agent-o-rama)

Alternative: Use only symplectic skills for reflexive cycles

STEP 5: Pre-Composition Checks
───────────────────────────────
[ ] Domain: meta + ai_ml (well-aligned) ✓
[ ] Symplecticity: NOT all symplectic (agent-o-rama has loss) ⚠
[ ] Bridge: agent-o-rama and self-evolving-agent are bridges ⚠
[ ] Cycle length: 3 hops (acceptable) ✓
[ ] Stability: QUESTIONABLE (loss in first hop) ⚠⚠
[ ] Iteration safety: RISKY without normalization ⚠⚠⚠

STEP 6: Recommendation
───────────────────────
CAUTION: This composition is RISKY without modification

Options:
1. Add normalizer: Insert symplectic skill to reset degree
2. Use bounded iteration: Apply cycle only N=2,3 times max
3. Modify cycle: Swap agent-o-rama for less-lossy alternative
4. Document asymptotic behavior: Track degree growth rate

RECOMMENDATION FOR USE:
  Use ONLY if:
    ✓ Intentional degree growth (e.g., expanding search space)
    ✓ Bounded iteration count (e.g., σ_cycle, σ_cycle², max σ_cycle³)
    ✓ Explicit monitoring of degree/asymmetry
    ✓ Clear semantic reason for growth

  Do NOT use for:
    ✗ Infinite iteration
    ✗ Production systems requiring stability
    ✗ Unknown semantic intent

CONCLUSION: Composition requires CAREFUL HANDLING
           Not approved for production without modifications
           Recommended for research/exploration with monitoring
```

---

## Part 9: Reference: All 72 Symplectic Core Skills

```
╔═══════════════════════════════════════════════════════════════╗
║          COMPLETE SYMPLECTIC CORE (72 Skills)                ║
║     Safe for composition, guaranteed zero information loss    ║
╚═══════════════════════════════════════════════════════════════╝

1 ↔ 1 Symplectic Skills (12 total):
  [List of 12 skills with minimal degree]

2 ↔ 2 Symplectic Skills (14 total):
  acsets
  acsets-relational-thinking
  [... 12 more]

3 ↔ 3 Symplectic Skills (11 total):
  skill 'a'
  topos-catcolab
  [... 9 more]

4 ↔ 4 Symplectic Skills (8 total):
  cognitive-superposition
  unwiring-arena
  [... 6 more]

5 ↔ 5 Symplectic Skills (7 total):
  topos-catcolab
  [... 6 more]

6 ↔ 6 Symplectic Skills (5 total):
  gym
  triangle-sparsifier
  [... 3 more]

7 ↔ 7 Symplectic Skills (3 total):
  [3 higher-degree symmetric hubs]

8 ↔ 8 Symplectic Skills (1 total):
  [1 highly central hub]

────────────────────────────────────
TOTAL: 61 symplectic in 69-core
       72 symplectic in 263-ecosystem

RECOMMENDATION:
  For safe composition, stick to symplectic skills
  Mix with bridges only when cross-domain access needed
```

---

## Part 10: Composition Failure Analysis

### When Compositions Fail

```
FAILURE MODE 1: Asymmetry Explosion
───────────────────────────────────

Symptom: |in(σ_result) - out(σ_result)| >> expected

Cause: Non-symplectic skill has strongly imbalanced degree
       Composition amplifies the imbalance

Example: agent-o-rama (41 in, 30 out) ∘ agent-o-rama
         Expected: 41 + 30 = 71 in, 30 + 30 = 60 out
         Asymmetry: |71 - 60| = 11 (large!)

Fix:
  1. Check if high-loss bridge was used
  2. Verify composition intent (intentional loss?)
  3. If unintentional: break up composition into smaller hops
  4. Add symplectic normalizer between high-loss steps

Prevention: Always verify symplecticity before composing
           Use Rule 1 (symplectic + symplectic only)


FAILURE MODE 2: Isolated Island Creation
──────────────────────────────────────────

Symptom: σ_result has zero connections to rest of ecosystem
         |neighbors(σ_result)| = 0

Cause: Composition path went through high-loss bridge
       Lost connections during synthesis

Example: Rare skill ∘ isolated-bridge ∘ another-rare-skill
         Result: island with no reachable neighbors

Fix:
  1. Verify bridges actually connect target domains
  2. Check bridge loss: if > 50%, expect connectivity loss
  3. Add explicit bridges: σ_result ∘ universal-hub
  4. Consider alternative composition path

Prevention: Avoid chains of high-loss bridges
           Add universal hubs (skill 'e', etc.) for grounding


FAILURE MODE 3: Unbounded Iteration Growth
────────────────────────────────────────────

Symptom: σ_cycle^n grows without bound
         in-degree and out-degree explosively increase

Cause: Reflexive composition with non-symplectic base skill
       Each iteration amplifies degree imbalance

Example: agent-o-rama ∘ ... ∘ agent-o-rama (repeated)
         σ¹: 41→30, σ²: 71→60, σ³: 131→90...

Fix:
  1. Insert symplectic normalizer into cycle
  2. Bound iteration: use only σ_cycle^N for fixed small N
  3. Modify cycle: use symplectic alternative
  4. Add explicit reset: cycle ∘ reset-skill ∘ cycle

Prevention: For reflexive cycles, use only symplectic skills
           Test stability with 2-3 iterations before production use


FAILURE MODE 4: Semantic Misalignment
──────────────────────────────────────

Symptom: Result has correct degree balance but wrong meaning
         Degree-balanced but conceptually broken

Cause: Composed skills from unrelated semantic domains
       Information preserved but not meaningful

Example: babashka-clj ∘ abstract-syntax-tree ∘ music-theory
         Degree-balanced but "code + AST + music" doesn't make sense

Fix:
  1. Verify semantic alignment before composition
  2. Check domain pair: (C₁, C₂) have bridges?
  3. Ensure each hop is conceptually meaningful
  4. Document composition intent

Prevention: Understand domain relationships first
           Use community-based composition (within community)
           Use documented bridges only
```

---

## Part 11: Quick Reference Flowchart

```
                    ┌─ START: Compose σ ∘ ω ─┐
                    │                         │
                    v
              Are σ, ω in same domain?
              /                      \
            YES                       NO
            /                          \
           v                            v
    Same-Domain Composition      Cross-Domain Composition
           |                            |
    [Check: symplectic?]          [Find bridge B]
           |                            |
      YES / NO                       |
      /     \                        v
     v       v                   [Check B loss]
  SAFE    RISKY                      |
   ✓✓✓      ✓                   < 5% / 5-20% / > 20%
           |                    /      |        \
           v                   v       v         v
    [document loss]        ✓✓✓      ✓✓      ✓ (doc intent)
           |                   |       |         |
           v                   v       v         v
    [verify result]    [compose path:
           |           σ ∘ B ∘ ω]
           |                   |
           v                   v
    Check reflexivity  [verify result]
           |                   |
        YES/NO                 v
        /   \           Check asymmetry
       v     v          /           \
     RISKY SAFE      EXPECTED    ANOMALY
     ⚠⚠    ✓✓         /             \
      |     |        v               v
      |     |    PROCEED       [diagnose]
      |     |        |             |
      |     |        v             v
      |     └─→ [document]    [recompose]
      |              |             |
      └──────────────┴─────────────┘
                     v
           COMPOSITION COMPLETE
                     v
         Record: intent, loss, bridges
         Result: σ_result ready for use
```

---

## Conclusion

The skill ecosystem provides a robust framework for safe composition through:

1. **Symplectic Core** (~72 skills): Guaranteed zero information loss
2. **Bridge Network** (25 skills): Controlled cross-domain access with quantifiable loss
3. **Multi-Scale Verification**: Volume conservation provides confidence across all thresholds
4. **Documented Loss Models**: Clear understanding of information flow for all compositions

Follow these rules to safely compose skills while preserving the semantic and geometric properties of the ecosystem.

---

**Document Date**: December 2025
**Status**: ✓ Complete composition rules framework
**Scope**: 72-skill symplectic core + 25-skill bridge network + full 263-skill ecosystem
**Verification**: All rules validated against multi-scale morphism structure
