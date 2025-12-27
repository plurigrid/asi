# Emily Riehl: Formalizing Post-Rigorous Mathematics
## Comprehensive Analysis & Framework

---

## I. CORE CONCEPT: POST-RIGOROUS MATHEMATICS

### Tao's Three Stages of Mathematical Development

1. **Pre-rigorous stage**
   - Informal, intuitive, example-based
   - Fuzzy notions and hand-waving
   - Emphasis on computation
   - Early undergraduate years

2. **Rigorous stage**
   - Precise, formal thinking required
   - Manipulation of abstract objects
   - Emphasis on theory
   - Later undergrad & early graduate

3. **Post-rigorous stage** (aspirational)
   - Comfortable with rigorous foundations
   - Revisits pre-rigorous intuition with rigor backing it
   - Emphasis: applications, intuition, big picture
   - Late graduate years and beyond
   - **Domain-specific**: expert only in specific field

### Riehl's Redefinition (Practical)

Post-rigorous arguments in practice are those that:
- Are not explained in full detail
- Contain claims that "might not quite be true as stated"
- Are "morally correct" or "globally true" despite local errors
- Propagate errors that cancel out later

This is **not aspirational**—it's what actually appears in mathematical literature.

---

## II. FOUR CASE STUDIES FROM INFINITY CATEGORY THEORY

### Case 1: Kapranov-Voevodsky (1991) vs. Simpson (1998)

**The Problem:**
- Paper: "Infinity Groupoids and Homotopy Types"
- Concerns: Homotopy hypothesis
- Issue: Simpson showed their result was contradictory (3-type of S²)
- Voevodsky remained confident until **fall of 2013** (15 years later!)
- Root cause: Subtle identity issues, no easily identifiable error point

**Implication for Formalization:**
- Formal verification would have caught the error
- Computer proof assistant forces justification at each step
- Voevodsky later moved to formal proof systems after this experience

---

### Case 2: Lurie's "On Infinity Topoi" (Pre-print)

**The Approach:**
- 100-page paper on infinity categories
- Deliberately avoids precise definition of infinity categories
- Uses intuitive sketches instead
- Quote: "rather than single out one foundation... explain the ideas involved... experts will be able to fill in the details"

**What Happened:**
- Community pushed back
- Not enough experts to fill in details
- Later book version forced to be more rigorous
- Had to prove theorems for concrete model

**Implication for Formalization:**
- Axiomatic approach needed (define Infinity Cosmos)
- Define infinity category as object in abstract universe
- Avoids choosing specific model upfront
- Feasible: but requires proving models exist (hard)

---

### Case 3: Cobordism Hypothesis (Baez-Dolan)

**Status:**
- Conjectured in 1990s
- "Proved" by Hopkins-Lurie (dimension 2) and Lurie (higher dimensions)
- Lurie's proof: **only exists as detailed sketch**
- Footnote admits: "proof has only appeared as a sketch"

**The Question:**
- Has it been proven or not?
- No clear consensus
- 2023 MathOverflow: still no definitive answer

**Implication for Formalization:**
- Hard to formalize from sketches
- Sketches often lack precise definitions
- Possible: "formalized blueprint" approach (architecture visible, gaps marked)
- Would clarify exactly what remains to be proven

---

### Case 4: Gaitsgory-Rozenblyum (Derived Algebraic Geometry)

**The Approach:**
- 1000+ page, two-volume work
- Explicitly lists 7 unproven statements
- Footnote: "existing literature in Infinity 2 categories does not contain proofs of all statements we need"

**Implication for Formalization:**
- **Totally formalizable**
- Just state assumptions and prove consequences
- Similar to Gates approach: mark holes explicitly
- Actually had positive effect: spawned research filling the gaps

---

## III. FORMALIZATION STRATEGIES

### Strategy 1: Concrete Model in Set Theory (Lean/Mathlib)

**Approach:**
- Define initial/terminal objects precisely
- Define fiber, cofiber, pullback, pushout formally
- Prove all lemmas (e.g., pullback composition & cancellation)
- Handle families of elements carefully

**Pros:**
- Grounded in well-established framework
- Practical precedent in Lean community

**Cons:**
- Significant implementation work
- Must choose specific model of infinity categories
- May not scale to higher categories

**Economics:** High upfront cost, but complete formalization

---

### Strategy 2: Axiomatic/Abstract (Infinity Cosmos)

**Approach:**
- Define Infinity Cosmos (abstract universe where infinity categories live)
- Define axioms sufficient to prove everything
- Define infinity category as object in cosmos
- Don't commit to specific model initially

**Pros:**
- Theorems proven once apply to all models
- Works for quasi-categories, condensed mathematics, etc.
- Matches mathematical practice better

**Cons:**
- Economics: hard to prove models exist
- Once model proven to satisfy axioms, all theorems transfer for free
- Payoff is worth it for multiple models

**Economics:** High cost in proving models exist, massive payoff for generality

---

### Strategy 3: Synthetic Type Theory (Domain-Specific)

**Approach:**
- Avoid set-based models entirely
- Develop infinity category theory synthetically
- Use "generalized elements" = terms in context
- Element-wise construction becomes rigorous in formal system

**Pros:**
- Informal and formal proofs very close
- Natural alignment with how mathematicians think
- Post-rigorous element-wise proof becomes rigorous

**Cons:**
- Requires bespoke proof assistant (e.g., Rzk)
- Can't use standard Lean/Coq infrastructure
- Must trust experts for interpretation into set theory

**Economics:** Different tradeoff—accept alternate foundation if clarity gained

---

## IV. THE ECONOMICS QUESTION

**Key Insight (from audience member):** This isn't primarily a correctness question—it's an **economics question**

### Historical Precedent: Grothendieck Model
- In master's programs, students would take one section from Grothendieck's paper
- Each section became one master's thesis
- Took years to work out all details rigorously

### Current Economics
- Famous mathematicians (Voevodsky, Tao, Lurie) can publish post-rigorous work that counts as proof
- Others cannot get same credit
- Formal verification makes this distinction clearer and more fair

### Future Possibility
- Clear separation: what's proven vs. what remains
- Credit flows to person who formalizes/completes
- Reduces sociological advantage of fame

---

## V. CASE STUDY: STABLE INFINITY CATEGORIES

### The Definition (Post-Rigorous)
A pointed infinity category is **stable** if:
- Every morphism has both fiber and cofiber (pullback & pushout)
- Fiber and cofiber squares coincide

### The Proposition
Stable infinity categories admit:
- All pushouts and pullbacks
- Every pullback is a pushout (and vice versa)

### The Post-Rigorous Proof (1 paragraph)
```
Given cofibration f:
1. Form cofiber square (by definition of stable)
2. By stability, it's also a fiber square
3. Form pullback of full rectangle
4. By pullback cancellation, right square is pullback
∴ pushouts & pullbacks exist and coincide
```

### The Rigorous Elaboration (multiple pages)
- Explain "generic family of cospans"
- Define how to work with families of elements vs. single elements
- Use generalized elements (= terms in context)
- Extend to functors between infinity categories
- Handle coherence requirements explicitly

### Why This Matters
- Shows gap between how mathematicians think (element-wise)
- And what's technically required (functorial, coherent)
- Formalization must bridge this gap

---

## VI. IMPLICATIONS & TENSIONS

### 1. Correctness vs. Notation
- Local errors are NOT fine (Riehl is clear: "incorrect proof is not a proof")
- But errors can be "morally correct" globally
- Formalization clarifies distinction

### 2. Foundations Matter
- Can't avoid set theory? Use Lean/Mathlib
- Want abstract axioms? Use Infinity Cosmos framework
- Want natural presentation? Need synthetic type theory (Rzk)

### 3. Expertise as Hidden Assumption
- Literature assumes reader can fill in gaps
- Only possible if reader is expert
- Formalization makes hidden requirements explicit

### 4. Economics of Rigor
- Full rigor is expensive
- Full sketchiness creates ambiguity
- Formalized blueprint (architecture + gaps) is middle ground

---

## VII. KEY REFERENCES & CONCEPTS

### People
- Terry Tao: concept of post-rigorous mathematics
- Emily Riehl: modern infinity category theory & formalization
- Jacob Lurie: foundational infinity category theory works
- Vladimir Voevodsky: motivated to formalize after proof errors
- Gaitsgory-Rozenblyum: transparent gap-marking in 2000+ page work

### Concepts
- **Homotopy hypothesis**: infinity groupoids ≅ homotopy types
- **Infinity Cosmos**: abstract universe for infinity categories
- **Sketch proofs**: detailed but not complete proofs
- **Generalized elements**: families of elements indexed by arbitrary objects
- **Coherence requirements**: compatibility conditions in higher categories

### Proof Assistants
- Lean/Mathlib: set theory-based, practical
- Rzk: synthetic type theory for infinity categories
- Coq: general purpose (not mentioned but relevant)

---

## VIII. OPEN QUESTIONS

1. Can sketch proofs be formalized? (Partial answer: yes, if architecture is clear)
2. Should formalization be mandatory? (Economics question)
3. How to credit intermediate work? (Formalization helps here)
4. Which foundation best serves formalization? (Problem-dependent)
5. What's the minimal "post-rigorous to rigorous" cost for different fields?

---

## IX. SYNTHESIS

**The Core Tension:**
Mathematics advances through post-rigorous exploration (fast, intuitive, efficient).
But verification requires rigor (slow, detailed, complete).

**The Formalization Promise:**
Make the boundary clear. Reward both:
- The explorer (post-rigorous sketch)
- The rigorous verifier (formal proof)

**The Path Forward:**
- Axiomatic frameworks (Strategy 2) for maximum generality
- Synthetic type theory (Strategy 3) for natural presentation
- Strategic formalization of key gaps (like Gaitsgory-Rozenblyum)
