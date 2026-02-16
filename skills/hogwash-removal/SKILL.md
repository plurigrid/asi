---
name: hogwash-removal
version: 1.0.0
description: Audit code and documentation for mathematical cargo-culting, inflated claims, and category-theoretic hogwash. Use when reviewing READMEs, module docs, comments, or papers that reference category theory, type theory, or abstract math. Detects misuse of technical terminology, analogy-dressed-as-theorem, name-dropping citations, and overclaimed novelty.
---

# Hogwash Removal

> "Category theory is an extremely insightful subject but its generality,
> the plethora of structural heuristics it provides, as well as its apparent
> conceptual simplicity make it very prone to cargo-culting."
> -- Matteo Capucci, "No, the Yoneda Lemma Doesn't Solve the Problem of Qualia" (2023)

**Trit**: -1 (VALIDATOR)
**Color**: #E84040 (Red)
**Status**: Production Ready

## What This Skill Does

Given a codebase or document, systematically audit every mathematical claim against these criteria:

1. **Is the terminology used correctly?** (e.g., "topos" means a specific thing, not "any structure")
2. **Is the claim a theorem or an analogy?** If analogy, is it labeled as such?
3. **Are citations relevant?** Does the cited work actually support the claim?
4. **Is novelty overclaimed?** Is this a straightforward instance of a known construction?
5. **Does the code match the math?** Is the implementation what the docs say it is?

## The Hogwash Scoring Rubric

Score each claim 0-10:

| Score | Meaning | Action |
|-------|---------|--------|
| 0 | Correct, precisely stated | Keep |
| 1-2 | Minor imprecision, reasonable shorthand | Note but keep |
| 3-4 | Slightly oversold but defensible | Add qualifier |
| 5-6 | Analogy presented as theorem, or trivial result presented as novel | Rewrite |
| 7-8 | Technical term misused, cargo-cult citation | Remove or replace |
| 9-10 | Fabricated mathematical claim, actively misleading | Delete and explain why |

## Common Hogwash Patterns

### Pattern 1: Topos/Site Name-Dropping (severity: 7-8)

**Symptom**: "X IS the site", "Y IS the classifying topos" where X and Y are not sites/toposes.

**Why it's hogwash**: A site is a category with a Grothendieck topology. A topos is a category with finite limits, power objects, and a subobject classifier. Using these words for things that aren't them is like calling a bicycle a "jet engine" because both involve wheels.

**Fix**: Use honest language. "Different semirings give different views" not "the semiring IS the site."

**Reference**: Caramello (2017) defines sites precisely. Capucci warns about this in his qualia post.

### Pattern 2: Trivial Instance Presented as Novel (severity: 5-6)

**Symptom**: "We fill a gap by combining X and Y" where X(Y) is a one-line instantiation.

**Why it's hogwash**: If your "novel combination" is just instantiating a known construction at a specific parameter, the gap is shallow. The engineering may be valuable but the math isn't new.

**Example from graded-optic**: `GradedOptic g s t a b` is literally `Optic_{Kl(Writer g)}(s,t,a,b)`. The "gap" between graded monads and optics is bridged by a single observation: use the Kleisli category of Writer g as your base.

**Fix**: Say "concrete library combining..." not "novel construction filling a gap."

### Pattern 3: Name Attribution Inflation (severity: 3-4)

**Symptom**: Attributing a standard construction to a specific researcher to sound more authoritative.

**Example**: "Hedges' teleological counit" for a standard existential quantification that every optics library uses. Hedges did important work on open games, but the existential residual in optics predates him (it's the coend variable in Riley's formulation).

**Fix**: Cite the mathematical object, not a researcher's name, unless they actually introduced it.

### Pattern 4: Citation Mismatch (severity: 7)

**Symptom**: Citing a paper/book that doesn't support the claim.

**Example**: Citing Caramello's *Theories, Sites, Toposes* for a construction that involves no Grothendieck topologies, geometric theories, or actual toposes.

**Fix**: Only cite works whose actual content supports your claim. If you're inspired by an analogy, say "inspired by" not "following."

### Pattern 5: Forward-Only → "Bayesian" Inflation (severity: 3-4)

**Symptom**: Calling any use of `Log Double` "Bayesian inference."

**Why it's hogwash**: Bayesian inference involves priors, likelihoods, conditioning, and posterior computation. Multiplying log-domain weights is likelihood accumulation, not inference. monad-bayes actually does Bayesian inference (with sampling, MH, SMC). Using its weight type doesn't inherit its capabilities.

**Fix**: Say "log-likelihood accumulation" or "log-domain scoring."

### Pattern 6: "Novel" Para (severity: 3)

**Symptom**: Calling a parametrised lens "the Para construction."

**Why**: Capucci/Gavranović's Para is a category with morphisms `(P, f: P.X → Y)` — forward only. Adding a backward channel makes it a parametrised optic or "learner" (Fong/Gavranović). These are different things.

**Fix**: Say "parametrised lens with backward channel" or "learner in the sense of Gavranović" if it has both directions.

### Pattern 7: Compositionality Assumed (severity: 4-5)

**Symptom**: Claiming a construction "composes" without proving it satisfies category laws.

**Reference**: Capucci (2023) explicitly warns: "Behaviours are not compositional on the nose." Theories of behaviour are only lax functorial. Compositionality is a theorem, not a given.

**Fix**: If you claim composition, prove identity and associativity laws (or at least test them).

## Audit Procedure

1. **Collect all mathematical claims** from README, module docs, comments, and examples
2. **For each claim, identify**: the mathematical object referenced, the technical terms used, the novelty assertion
3. **Check against primary sources**: Does the cited paper define the term this way? Is the construction actually what's claimed?
4. **Score each claim** using the rubric
5. **Produce a table**: Claim | Score | Why | Fix
6. **Apply fixes**: Replace hogwash with honest language. The code doesn't change — only the words around it.

## Key References for Checking Claims

- **Optics**: Riley (2018) "Categories of Optics", Capucci (2022) "Optics in Three Acts"
- **Para**: Capucci (2021) "Open Cybernetic Systems II", Gavranović (2024) PhD thesis Ch. 3
- **Cybernetics**: Capucci, Gavranović, Hedges, Rischel (2021) "Towards Foundations of Categorical Cybernetics"
- **Graded monads**: Katsumata (2014), Orchard/Wadler/Eades "Unifying graded and parameterised monads"
- **Actegories**: Capucci & Gavranović (2022) "Actegories for the Working Amthematician"
- **Contextads**: Capucci & Myers (2024) "Contextads as Wreaths" — the actual state of the art for grading in optics
- **Sites/Toposes**: Caramello (2017) "Theories, Sites, Toposes" — what sites actually are
- **Anti-cargo-cult**: Capucci (2023) "No, the Yoneda Lemma Doesn't Solve the Problem of Qualia"

## Bidirectional Neighbor Index

| Neighbor | Direction | Scope |
|----------|-----------|-------|
| `aristotle-lean` | outgoing | scope:verify — formal verification of claims |
| `code-review` | bidirectional | scope:compose — hogwash check as part of review |
| `refuse-mediocrity` | incoming | scope:change — mediocre framing triggers audit |
| `accept-no-substitutes` | bidirectional | scope:verify — honest terminology |
| `acsets-algebraic-databases` | outgoing | scope:verify — check ACSet claims |
| `open-games` | outgoing | scope:verify — check game theory claims |
| `discopy-operads` | outgoing | scope:verify — check categorical claims |

## GF(3) Triad

`hogwash-removal` (-1) + `refuse-mediocrity` (+1) + `code-review` (0) = 0

The validator (-1) catches inflated claims, the generator (+1) pushes for better framing, the ergodic coordinator (0) integrates both into the review process.

## Example: graded-optic Audit (2026-02-08)

Applied to plurigrid/graded-optic. Results:

| Claim | Before | After | Score |
|-------|--------|-------|-------|
| "semiring IS the site" | Cargo-cult Caramello | Removed entirely | 8→0 |
| "optic IS the classifying topos" | False | Removed entirely | 8→0 |
| Caramello citation | Irrelevant | Removed | 7→0 |
| "Novel gap" | Oversold | "Concrete library combining..." | 5→1 |
| "Hedges' teleological counit" | Name-drop | "coend variable in the optic formula" | 4→1 |
| "Bayesian bidirectional inference" | Inflated | "log-likelihood accumulation" | 3→0 |
| Para attribution | Slightly loose | "Extends Para with backward channel" | 3→1 |
| Composition (|>>>|) | Correct | Unchanged | 0→0 |
| Examples | Honest | Unchanged | 1→1 |

**Net effect**: Average hogwash score dropped from 4.3 to 0.4.
