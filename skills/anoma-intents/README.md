# Anoma Intents Skill

> *"Declare what you want, not how to get it. The solver finds the path."*

## Overview

**Anoma Intents** implements intent-centric architecture for cross-chain obstruction passing with Geb semantics and Juvix compilation. Users specify desired outcomes; solvers find valid execution paths.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | +1 (PLUS) |
| Role | GENERATOR |
| Function | Generates intents that solvers satisfy |

## Core Concepts

### Intent Structure

```juvix
type Intent :=
  | Swap : Asset -> Asset -> Quantity -> Quantity -> Intent
  | Transfer : Address -> Address -> Asset -> Quantity -> Intent
  | Delegate : Address -> ValidatorSet -> Intent
  | Compound : Intent -> Intent -> Intent;

-- Intents are declarative, not imperative
-- "I want X" not "Do A then B then C to get X"
```

### Solver Interface

```juvix
type Solution :=
  mkSolution {
    intent : Intent;
    transactions : List Transaction;
    proof : ValidityProof;
    cost : Resource;
  };

solve : Intent -> Maybe Solution;
solve intent :=
  let candidates := enumerate-execution-paths intent in
  find valid-and-optimal candidates;
```

## Geb Semantics

Anoma uses Geb (Graph-based Executable semantics) for intent specification:

```
Intent = Graph of resource transformations
Solver = Path finder in resource graph
Solution = Valid path from current state to desired state
```

### Resource Logic

```juvix
-- Resources are linear (used exactly once)
type Resource :=
  mkResource {
    label : Label;
    quantity : Nat;
    owner : Address;
    logic : ResourceLogic;  -- Validity predicate
  };

-- Conservation law: inputs balance outputs
check-conservation : Transaction -> Bool;
check-conservation tx :=
  sum (map quantity tx.inputs) == sum (map quantity tx.outputs);
```

## Juvix Compilation

Intents compile from high-level Juvix to Anoma's execution layer:

```
Juvix Intent DSL
      ↓ (type-checked)
Geb Semantics Graph
      ↓ (optimized)
Anoma Resource Machine
      ↓ (solved)
Cross-chain Transactions
```

## Cross-Chain Obstruction

```
┌─────────────────────────────────────────────────────────────────┐
│                    INTENT FLOW                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  User Intent                Solver                 Execution    │
│  ───────────               ────────               ───────────   │
│  "Swap 100 USDC    →    Find path:           →   Chain A: ...  │
│   for best ETH"         Chain A → Bridge         Bridge: ...   │
│                         → Chain B                Chain B: ...  │
│                                                                 │
│  Cross-chain obstructions are resolved by solver,              │
│  not specified by user                                          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## GF(3) Triads

```
anoma-intents (+1) ⊗ solver-fee (0) ⊗ intent-sink (-1) = 0 ✓
anoma-intents (+1) ⊗ datalog-fixpoint (0) ⊗ merkle-validation (-1) = 0 ✓
```

## Integration

```clojure
;; Babashka intent specification
(defn swap-intent [from-asset to-asset amount]
  {:type :swap
   :from {:asset from-asset :min-amount amount}
   :to {:asset to-asset}
   :constraints {:slippage-max 0.01
                 :deadline (+ (now) 3600)}})

;; Submit to Anoma solver
(defn submit-intent [intent]
  (-> intent
      (compile-to-geb)
      (submit-to-mempool)
      (await-solution)))
```

## Commands

```bash
# Compile Juvix intent
juvix compile intent.juvix -o intent.geb

# Submit to local solver
anoma-cli submit --intent intent.geb

# Check solution status
anoma-cli status --intent-id <id>
```

---

**Skill Name**: anoma-intents
**Type**: Intent-Centric Architecture
**Trit**: +1 (PLUS - GENERATOR)
**GF(3)**: Generates intents for solver satisfaction
