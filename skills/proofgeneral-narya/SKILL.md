---
name: proofgeneral-narya
description: "Proof General + Narya: Higher-dimensional type theory proof assistant with observational bridge types for version control."
license: GPL-3.0
metadata:
  trit: -1
  source: ProofGeneral/PG + mikeshulman/narya + music-topos
  xenomodern: true
  stars: 768
---

# ProofGeneral + Narya Skill

> *"Observational type theory: where equality is what you can observe, not what you can prove."*

## Overview

This skill combines:
- **Proof General** (543⭐): The universal Emacs interface for proof assistants
- **Narya** (225⭐): Higher-dimensional type theory proof assistant

## Proof General Basics

```elisp
;; Install via straight.el or package.el
(use-package proof-general
  :mode ("\\.v\\'" . coq-mode)
  :config
  (setq proof-splash-enable nil
        proof-three-window-mode-policy 'hybrid))
```

### Key Bindings

| Key | Action | Description |
|-----|--------|-------------|
| `C-c C-n` | `proof-assert-next-command-interactive` | Step forward |
| `C-c C-u` | `proof-undo-last-successful-command` | Step backward |
| `C-c C-RET` | `proof-goto-point` | Process to cursor |
| `C-c C-b` | `proof-process-buffer` | Process entire buffer |
| `C-c C-.` | `proof-goto-end-of-locked` | Jump to locked region end |

### Proof State Visualization

```
┌─────────────────────────────────────────────────────────────┐
│  ████████████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  │
│  ▲ Locked (proven)   ▲ Processing      ▲ Unprocessed       │
│                                                             │
│  GF(3) Trit Mapping:                                        │
│    Locked    → +1 (LIVE)     → Red    #FF0000              │
│    Processing → 0  (VERIFY)  → Green  #00FF00              │
│    Unprocessed → -1 (BACKFILL) → Blue #0000FF              │
└─────────────────────────────────────────────────────────────┘
```

## Narya: Higher-Dimensional Type Theory

Narya is a proof assistant for higher observational type theory (HOTT).

### Key Features

1. **Observational Equality**: Bridge types computed inductively from type structure
2. **Higher Dimensions**: Support for 2-cells, 3-cells, etc.
3. **No Interval Type**: Unlike cubical type theory, no explicit interval

### Narya Syntax

```narya
-- Define a type
def Nat : Type := data [
  | zero : Nat
  | suc : Nat → Nat
]

-- Bridge type between values
def bridge (A : Type) (x y : A) : Type := x ≡ y

-- Transport along bridge
def transport (A : Type) (P : A → Type) (x y : A) (p : x ≡ y) : P x → P y
  := λ px. subst P p px
```

## Observational Bridge Types (gay.el integration)

From `narya_observational_bridge.el`:

```elisp
(cl-defstruct (obs-bridge (:constructor obs-bridge-create))
  "An observational bridge type connecting two versions."
  source      ; Source object
  target      ; Target object  
  bridge      ; The diff/relation between them
  dimension   ; 0 = value, 1 = diff, 2 = conflict resolution
  tap-state   ; TAP state: -1 BACKFILL, 0 VERIFY, +1 LIVE
  color       ; Gay.jl color
  fingerprint) ; Content hash

;; Create diff as bridge type
(defun obs-bridge-diff (source target seed)
  "Create an observational bridge (diff) from SOURCE to TARGET."
  (let* ((source-hash (sxhash source))
         (target-hash (sxhash target))
         (bridge-hash (logxor source-hash target-hash))
         (index (mod bridge-hash 1000))
         (color (gay/color-at seed index)))
    (obs-bridge-create
     :source source
     :target target
     :bridge (list :from source-hash :to target-hash)
     :dimension 1
     :color color)))
```

## Hierarchical Agent Structure: 3×3×3 = 27

```
Level 0: Root (VERIFY)
    │
    ├── Level 1: BACKFILL (-1) ─── L2: [-1, 0, +1] ─── L3: 3×3 = 9 agents
    ├── Level 1: VERIFY (0)    ─── L2: [-1, 0, +1] ─── L3: 3×3 = 9 agents  
    └── Level 1: LIVE (+1)     ─── L2: [-1, 0, +1] ─── L3: 3×3 = 9 agents

Total: 1 + 3 + 9 + 27 = 40 agents (or 27 leaves)
```

### Bruhat-Tits Tree Navigation

```elisp
;; Navigate the Z_3 gamut poset
(defun bt-node-child (node branch)
  "Return child of NODE at BRANCH (0, 1, or 2)."
  (bt-node (append (bt-node-path node) (list branch))))

(defun bt-node-distance (node1 node2)
  "Return tree distance between NODE1 and NODE2."
  (let* ((lca (bt-node-lca-depth node1 node2))
         (d1 (bt-node-depth node1))
         (d2 (bt-node-depth node2)))
    (+ (- d1 lca) (- d2 lca))))
```

## Möbius Inversion for Trajectory Analysis

```elisp
;; Map TAP trajectory to multiplicative structure
;; -1 → 2, 0 → 3, +1 → 5 (first three primes)
(defun moebius/trajectory-to-multiplicative (trajectory)
  (let ((result 1))
    (dolist (t trajectory)
      (setq result (* result
                      (pcase t
                        (-1 2)
                        (0 3)
                        (+1 5)))))
    result))

;; μ(n) ≠ 0 ⟹ square-free trajectory (no redundancy)
```

## Bumpus Laxity Measures

For coherence between proof states:

```elisp
(defun bumpus/compute-laxity (agent1 agent2)
  "Laxity = 0 means strict functor (perfect coherence).
   Laxity = 1 means maximally lax."
  (let* ((d (bt-node-distance (narya-agent-bt-node agent1)
                               (narya-agent-bt-node agent2)))
         (mu1 (narya-agent-moebius-mu agent1))
         (mu2 (narya-agent-moebius-mu agent2))
         (mu-diff (abs (- mu1 mu2))))
    (min 1.0 (/ (+ d (* 0.5 mu-diff)) 10.0))))
```

## Version Control Operations

| Operation | Description | Dimension |
|-----------|-------------|-----------|
| `fork` | Create 3 branches (balanced ternary) | 0 → 1 |
| `continue` | Choose branch (-1, 0, +1) | 1 → 1 |
| `merge` | Resolve conflict (2D cubical) | 1 → 2 |

## Xenomodern Stance

The ironic detachment here is recognizing that:

1. **Proof assistants are version control systems** for mathematical truth
2. **Type theory is a programming language** for proofs
3. **Observational equality** is more practical than definitional equality
4. **Higher dimensions** emerge naturally from conflict resolution

## Commands

```bash
just narya-demo           # Run Narya bridge demonstration
just proofgeneral-setup   # Configure Proof General
just spawn-hierarchy      # Create 27-agent hierarchy
just measure-laxity       # Compute Bumpus laxity metrics
```

## Starred Gists: Fixpoint & Type Theory Resources

### zanzix: Fixpoints of Indexed Functors
[Fix.idr](https://gist.github.com/zanzix/02641d6a6e61f3757e3b703059619e90) - Idris implementation of indexed functor fixpoints for graphs, multi-graphs, poly-graphs.

```idris
-- From zanzix gist: recursive structure via indexed Fix
data IFix : (f : (k -> Type) -> k -> Type) -> k -> Type where
  In : f (IFix f) i -> IFix f i
```

### VictorTaelin: ITT-Flavored CoC Type Checker
[itt-coc.ts](https://gist.github.com/VictorTaelin/dd291148ee59376873374aab0fd3dd78) - Intensional Type Theory Calculus of Constructions in TypeScript. Comment: "almost perfect! could make 8 lines shorter..."

### VictorTaelin: Affine Types
[Affine.lean](https://gist.github.com/VictorTaelin/5584036b0ea12507b78ef883c6ae5acd) - Linear/affine type experiments in Lean 4.

### rdivyanshu: Streams & Unique Fixed Points  
[Nats.dfy](https://gist.github.com/rdivyanshu/2042085421d5f0762184dd7fe7cfb4cb) - Dafny formalization of streams with unique fixpoint theorems.

### Keno: Abstract Lattice
[abstractlattice.jl](https://gist.github.com/Keno/fa6117ae0bf9eea3f041c0cf1f33d675) - Julia abstract lattice implementation. Comment: "a quantum of abstract solace ∞"

### norabelrose: Kronecker Decomposition
[kronecker_decompose.py](https://gist.github.com/norabelrose/3f7a553f4d69de3cf5bda93e2264a9c9) - Fast, optimal Kronecker decomposition algorithm.

### borkdude: UUID v1 in Babashka
[uuidv1.clj](https://gist.github.com/borkdude/18b18232c00c2e2af2286d8bd36082d7) - Deterministic UUID generation in Clojure/Babashka.

## QuickCheck ↔ Narya Bridge

Property-based testing and proof assistants share the **fixpoint structure**:

```
QuickCheck Arbitrary          Narya Type Formation
───────────────────          ──────────────────────
arbitrary :: Gen a            A : Type
shrink :: a -> [a]            transport : a ≡ b → P a → P b
Gen.recursive (tie)           data [ | zero | suc (Nat → Nat) ]
```

### Recursive Generators as Bridge Types

```haskell
-- QuickCheck-style recursive generator
genTree :: Gen Tree
genTree = sized $ \n ->
  if n == 0 then pure Leaf
  else oneof [ pure Leaf
             , Branch <$> resize (n `div` 2) genTree
                      <*> resize (n `div` 2) genTree ]

-- Maps to observational bridge in Narya
-- def Tree : Type := data [ | Leaf | Branch (Tree, Tree) ]
-- Bridge between trees = structural diff
```

## References

- [Proof General Manual](https://proofgeneral.github.io/)
- [Narya GitHub](https://github.com/mikeshulman/narya)
- [Higher Observational Type Theory](https://ncatlab.org/nlab/show/higher+observational+type+theory)
- [Topos Institute: Structure-Aware Version Control](https://topos.institute/blog/2024-11-13-structure-aware-version-control-via-observational-bridge-types/)
- [Towards Foundations of Categorical Cybernetics](https://arxiv.org/abs/2105.06332) - Capucci, Gavranović, Hedges, Rischel
