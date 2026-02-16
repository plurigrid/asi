# The Holes Skill: Interactive Proof Holes in Narya

**Skill Name:** `holes`
**Category:** verification
**GF(3) Trit:** MINUS (constraint/verification)
**Version:** 1.0.0

---

## What is a Hole?

A **hole** is Narya's mechanism for interactive proof development. It marks a place in your proof where you'll fill in a term later. Narya displays the hole's type and context, helping you understand what term is needed.

Two syntaxes:
- `?` - Simple hole (single token)
- `¿...ʔ` - Region hole (preserves interior text for documentation)

---

## Holes in Our Bridge Type Formalization

We have **11 proof stubs** across our formalization:

### Current Stubs

| File | Theorem | Stubs | Status |
|------|---------|-------|--------|
| BridgeType.lean | black_hole_absorption | 1 | 📋 Ready |
| BridgeType.lean | white_hole_divergence | 1 | 📋 Ready |
| BridgeType.lean | life_is_bridge_type | 1 | 📋 Ready |
| BridgeType.lean | three_mechanisms_compose | 1 | 📋 Ready |
| BridgeType.lean | gf3_conservation_universal | 1 | 📋 Ready |
| BridgeType.lean | ecosystem_satisfies_bridge_type | 1 | 📋 Ready |
| EcosystemBridgeType.lean | ecosystem_gf3_conserved | 1 | 📋 Ready |
| EcosystemBridgeType.lean | transition_preserves_identity | 1 | 📋 Ready |
| EcosystemBridgeType.lean | functional_invariance_in_transitions | 1 | 📋 Ready |
| EcosystemBridgeType.lean | ecosystem_is_bridge_type | 1 | 📋 Ready |
| ValveMechanism.lean | unworld_rhythm_periodic | 1 | 📋 Ready |

**Total: 11 holes ready to solve**

---

## Quick Hole Reference

### Basic Syntax

```lean
-- Simple hole
def my_theorem : Prop := ?

-- Region hole with documentation
def my_proof : A := ¿
  Proof by induction on structure of A.
  Base case: constructor
  Inductive: assume IH for smaller terms
ʔ

-- Multiple holes
def f : A := ?
def g : B := ?
def h : C := ?
```

### Hole Properties

| Property | Meaning |
|----------|---------|
| **Does not synthesize** | Hole doesn't infer its own type |
| **Checks against any type** | Hole is polymorphic in its type |
| **Generalized over context** | Treated as axiom with free variables |
| **Fails on equality constraints** | Cannot constrain value of hole |
| **Dependent argument restriction** | Cannot use in positions affecting output type |

### Key Restriction

**Cannot use holes in dependent positions:**

```lean
-- FAILS: Result type has ?
concat A ? ? ? ? ?  -- Type is Id A ? ? (contains ?'s)

-- OK: Provide non-dependent arguments
concat A a ? b ? ?  -- Type is Id A a b (fully determined)
```

---

## Interactive Proof Workflow

### 1. Write Theorem with Holes

```lean
theorem bridge_type_exists (sg : SkillGraph) :
  standard_gf3_distribution sg.skills →
  ∃ bridge : EcosystemBridgeType sg,
    bridge.state_old = sg ∧
    bridge.gf3_conserved ∧
    ∀ query : Skill, bridge.function_valid query := by
  intro h_dist
  ?  -- Proof goes here
```

### 2. Process Command (C-c C-n in ProofGeneral)

Narya shows:
```
Hole ?0:
Context: h_dist : standard_gf3_distribution sg.skills
Goal: ∃ bridge : EcosystemBridgeType sg, ...
```

### 3. Navigate Holes (C-c C-j / C-c C-k)

Jump between holes in the file to understand proof structure.

### 4. Split on Hole (C-c C-y)

Asks: "What should I split on?" and generates proof structure:

```lean
-- If you split on a datatype with constructors
-- Narya generates match expression with all branches

-- If no split term, generates from goal type
-- Example: Function type goal → generates abstraction
-- Example: Datatype goal → generates match
```

### 5. Solve Holes (C-c SPC)

Fill in actual proof term. Can contain new holes.

### 6. Continue Until Complete

Process next command to reveal new holes.

---

## ProofGeneral Commands for Holes

| Command | Key | Effect |
|---------|-----|--------|
| Show hole type/context | C-c , | Display in goals window |
| Solve hole | C-c SPC | Fill with term in hole region |
| Split on hole | C-c C-y | Generate structure from type |
| Synthesize term type | C-c : | Show type of term in hole |
| Normalize term | C-c ; | Evaluate term to normal form |
| Next hole | C-c C-j | Jump to next hole |
| Previous hole | C-c C-k | Jump to previous hole |

---

## Case Tree Holes

**Case tree holes:** Holes in positions where pattern matches are valid.

```lean
-- This is a case tree hole
def my_function : Result :=
  match data with
  | constructor1 args → ?    -- Case tree hole
  | constructor2 args → ?    -- Case tree hole
```

**Behavior:**
- Don't reduce during evaluation
- Display as function name + arguments (reparseable)
- More efficient than term holes

---

## Hole Solving Mechanics

### Contexts are Applied

When a hole has free variables, subsequent uses may apply substitutions:

```lean
-- Hole ?0 has context with variable x
-- Later uses of ?0 may substitute values for x
-- But substitution not displayed in output
```

### Display Format

```
?N{...}
 ↑    ↑
 |    Context variables (not fully shown)
 |
 Sequential hole number
```

### Important: Not Reparseable

The `?N{...}` notation **cannot be parsed again**. It's for display only.

---

## Workflow Patterns

### Pattern 1: Structural Induction

```lean
theorem prop_holds : ∀ x : Data, P x := by
  intro x
  ?  -- Structurally analyze x
  -- After split, get branches for each constructor
  -- Solve each branch independently
```

### Pattern 2: Chained Arguments

```lean
theorem compose_properties : ?  -- Main theorem hole

-- After solving, leads to:
theorem aux_lemma1 : ?          -- New hole in consequence
theorem aux_lemma2 : ?          -- New hole in consequence
```

### Pattern 3: Multiple Holes for Parts

```lean
theorem complete_proof : A ∧ B := ⟨?, ?⟩
-- Solve first ? for A
-- Solve second ? for B
```

---

## Example: Bridge Type Proof Stub

From `BridgeType.lean`:

```lean
/-- Theorem 1: Black Hole Absorption
    A system with only one constructor (refl) collapses to a fixed point. -/
theorem black_hole_absorption (α : Type u) (f : α → α) :
  (∀ a : α, f a = f (f a)) →
  ∃ fixed : α, ∀ a : α, (Nat.iterate f 100 a) = fixed := by
  intro h
  sorry -- Proof: Apply Banach fixed-point theorem
```

**To solve this hole:**

1. State the goal clearly
2. Apply relevant lemmas (Banach fixed-point theorem)
3. Handle the fixed function case
4. Show iteration converges

**Proof structure:**
```lean
theorem black_hole_absorption (α : Type u) (f : α → α) :
  (∀ a : α, f a = f (f a)) →
  ∃ fixed : α, ∀ a : α, (Nat.iterate f 100 a) = fixed := by
  intro h
  -- Split on α or apply Banach FPT
  -- Use assumption h to establish function is idempotent
  -- Conclude fixed point exists
  exact ⟨f a, sorry⟩  -- Fill in a and prove equivalence
```

---

## Managing 11 Proof Stubs

### Organization Strategy

1. **Group by complexity**
   - Simple: Arithmetic proofs (ecosystem_gf3_conserved)
   - Medium: Category theory (transition_preserves_identity)
   - Hard: Mechanism composition (mechanisms_maintain_coherence)

2. **Dependency order**
   - Prove simpler theorems first
   - Use as lemmas in complex proofs

3. **Test incrementally**
   - Solve 1-2 holes
   - Check Narya accepts your work
   - Continue with next group

### Checking All Holes

```bash
# Find all stubs
grep -n "sorry" formalization/*.lean

# Count by file
for f in formalization/*.lean; do
  echo "$f: $(grep -c 'sorry' $f) holes"
done

# View in context
grep -B5 "sorry" formalization/BridgeType.lean
```

---

## Hole Solving for Bridge Type

### Phase A.2-A.3 Approach

**Valve mechanism** (ValveMechanism.lean):
- 1 hole: Prove valve period is periodic
- 1 hole: Prove duty cycle is 50%
- 3 holes: Prove collapse/explosion prevention

**Filter mechanism** (FilterMechanism.lean):
- 4 holes: SPH kernel properties
- 3 holes: Convergence and constraint preservation

**Resurrector mechanism** (ResurrectorMechanism.lean):
- 5 holes: Recovery injection properties

**Composition** (MechanismComposition.lean):
- 2 holes: All three mechanisms together
- Main theorem: Complete system stability

---

## Next Steps

1. **Pick a hole to solve**
   - Start with `ecosystem_gf3_conserved` (arithmetic)
   - Proceed to `transition_preserves_identity` (category theory)

2. **Set up development environment**
   ```bash
   cd /Users/bob/ies/asi/formalization
   # Open BridgeType.lean in Emacs with ProofGeneral
   ```

3. **Use hole workflow**
   - Process file (C-c C-n)
   - Navigate holes (C-c C-j/C-c C-k)
   - Understand goal (C-c ,)
   - Try splitting (C-c C-y)
   - Solve (C-c SPC)

4. **Track progress**
   ```bash
   # After solving each hole
   git commit -m "proof: Solve [hole name] in [file name]"
   ```

---

## References

- **Narya Documentation:** https://arb.site/narya/
- **Holes Section:** https://arb.site/narya/interactive.html#holes
- **ProofGeneral:** https://proofgeneral.github.io/
- **Interactive Proof Tactics:** https://arb.site/narya/interactive.html

---

## This Skill in Context

The **holes** skill is a **MINUS trit** skill (verification/constraint):
- Enables rigorous proof development
- Ensures no proofs slip through without filling holes
- Maintains proof completeness guarantee
- Part of amp (MINUS) verification system in UNWORLD federation

**Related skills:**
- `narya-core` - Narya proof assistant fundamentals
- `lean-4-bridge-type` - Bridge Type formalization
- `proof-assistant-patterns` - Interactive proof patterns

---

**🔧 USE THIS SKILL TO: Fill the 11 proof stubs in Bridge Type formalization and advance phases A.2-D through complete mathematical proof.**
