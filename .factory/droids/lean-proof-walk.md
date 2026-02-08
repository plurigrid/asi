---
name: lean-proof-walk
description: GF(3)-balanced random walk through Lean proof states. Use when generating formal proof chains with parallel triad verification. Invokes 3 agents (Generator +1, Coordinator 0, Validator -1) to traverse proof space via prime geodesics.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Lean Proof Walk

Generate formal Lean 4 proof state chains using GF(3)-balanced random walks.

## Triad Structure

| Agent | Trit | Role | Action |
|-------|------|------|--------|
| Generator | +1 | Create | Propose next proof state |
| Coordinator | 0 | Transport | Formalize transition, derive seed |
| Validator | -1 | Verify | Check soundness, GF(3) conservation |

**Invariant**: `trit(G) + trit(C) + trit(V) = (+1) + 0 + (-1) = 0`

## State Chain Format

```
State N: Γ ⊢ G

where:
  Γ = context (hypotheses: x : τ, h : P)
  ⊢ = turnstile (entailment)
  G = goal (proposition to prove)
```

### Example Chain

```
State 0: a : ℤ, b : ℤ, h : a + b = 0 ⊢ b = -a

State 1: a : ℤ, b : ℤ, h : a + b = 0 ⊢ a + b - a = 0 - a

State 2: a : ℤ, b : ℤ, h : a + b = 0 ⊢ b = -a

State 3: No Goals
```

## Protocol

### 1. Initialize
```
seed := 0x42D (or user-provided)
state := State 0 with full context and goal
triad := spawn 3 parallel agents with trits {-1, 0, +1}
```

### 2. Walk Step (repeat until No Goals)
```
Generator (+1):  propose tactic τ, predict State n+1
Coordinator (0): formalize Γₙ ⊢ Gₙ  →  Γₙ₊₁ ⊢ Gₙ₊₁
Validator (-1):  verify transition sound, Σ trits = 0
Commit:          seed_{n+1} = hash(seed_n ⊕ state_n)
```

### 3. Terminate
```
State m = "No Goals" → QED
Emit: formal statement, informal proof, detailed proof, state chain
```

## Invocation

```
/lean-proof-walk "∀ a b : ℤ, a + b = b + a"
/lean-proof-walk --seed=1069 --theorem="commutativity of addition"
```

## Output Structure

1. **Formal Statement** (Lean 4 syntax)
2. **Informal Proof** (1-2 sentences)
3. **Detailed Informal Proof** (numbered steps)
4. **Chain of States** (with interleaved explanations)

## Tactics Vocabulary

| Tactic | State Transition |
|--------|------------------|
| `intro x` | `Γ ⊢ ∀x.P` → `Γ, x:τ ⊢ P` |
| `apply h` | `Γ, h:P→Q ⊢ Q` → `Γ ⊢ P` |
| `exact h` | `Γ, h:P ⊢ P` → `No Goals` |
| `rfl` | `Γ ⊢ a = a` → `No Goals` |
| `simp` | `Γ ⊢ P` → `Γ ⊢ P'` (simplified) |
| `ring` | `Γ ⊢ pol