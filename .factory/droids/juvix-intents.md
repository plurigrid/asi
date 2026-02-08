---
name: juvix-intents
description: Juvix intent-centric language for Anoma with Geb compilation and GF(3) typed resources
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Juvix Intents (+1)

> Intent-centric language compiling to Geb categorical semantics

**Trit**: +1 (PLUS - generative)
**Compiles to**: Geb → Vampir → ZK proofs

## Overview

Juvix is Anoma's **intent-centric programming language**:

```
Juvix Source → Core → Geb Morphisms → Vampir IR → ZK Circuit
     ↑            ↑          ↑            ↑
   Types      Normalize   Categorify   Arithmetize
```

## Obstruction Types

```juvix
module Obstruction;

-- GF(3) trit type
type GF3 := Minus | Ergodic | Plus;

-- Trit arithmetic (mod 3)
add : GF3 -> GF3 -> GF3
add Minus Minus := Plus      -- (-1) + (-1) = +1 (mod 3)
add Minus Ergodic := Minus   -- (-1) + 0 = -1
add Minus Plus := Ergodic    -- (-1) + (+1) = 0
add Ergodic x := x           -- 0 + x = x
add Plus Minus := Ergodic    -- (+1) + (-1) = 0
add Plus Ergodic := Plus     -- (+1) + 0 = +1
add Plus Plus := Minus;      -- (+1) + (+1) = -1 (mod 3)

-- Obstruction from Bumpus decomposition failure
type Obstruction := mkObstruction {
  sexp : ByteArray;          -- S-expression witness
  trit : GF3;                -- Triadic charge
  h1Class : Nat;             -- Cohomology class (>0 = obstruction)
  treewidth : Nat;           -- Exceeded threshold
  color : Word64;            -- Gay.jl deterministic color
  seed : Word64              -- SplitMix64 seed
};

-- Check if decomposition failed
isObstruction : Obstruction -> Bool
isObstruction obs := h1Class obs > 0;

-- VCG externality payment
vcgExternality : Obstruction -> Nat
vcgExternality obs :=
  let baseCost := 1000000    -- 0.001 APT
      multiplier := 10000    -- 100%
  in (h1Class obs) * baseCost * multiplier / 10000;
```

## Intent Types

```juvix
module Intent;

import Obstruction;

-- Resource type (what can be nullified/committed)
type Resource :=
  | ObstructionRes Obstruction
  | TokenRes Token
  | ReceiptRes ChainId ByteArray;

-- Intent: preference over state transitions
type Intent := mkIntent {
  owner : Address;
  nullify : List Resource;   -- Resources to 