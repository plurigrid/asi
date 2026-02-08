---
name: autopoiesis
description: Self-producing skill system combining ruler enforcement with skill self-evolution. Implements trifurcation-first imperative via nbb sexp invocation for idempotent agent instruction.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Autopoiesis: Self-Producing Agent Skills

**Trit**: 0 (ERGODIC - coordinator)  
**Color**: Green (#26D826)

## Overview

Autopoiesis (Greek: αὐτό "self" + ποίησις "creation") implements **self-producing agent instruction systems** by combining:

1. **Ruler**: Unified instruction propagation across 18+ coding agents
2. **Agent Skills Spec**: Homebrew-style skill installation  
3. **Trifurcation Discipline**: XOR-independent parallel execution
4. **nbb SEXP Invocation**: Idempotent enforcement via Babashka

## The Trifurcation-First Imperative

**CRITICAL RULE**: When spanning 3+ domains/files/languages, Amp MUST spawn 3 Task subagents BEFORE any read/grep/find operations.

### Mathematical Foundation

Based on **SplitMixTernary XOR-independence** and **GF(3) field conservation**:

```
cat(69, -1, 0, +1) → Three streams that sum to coherent result

GOLDEN = 0x9e3779b97f4a7c15
MIX1   = 0xbf58476d1ce4e5b9  
MIX2   = 0x94d049bb133111eb
SEED   = 0x42D  ;; 1069
```

| Stream | ID | Role | Action |
|--------|-----|------|--------|
| MINUS | -1 | Contracting | Search/Read |
| ERGODIC | 0 | Synthesis | Analyze (NO reading) |
| PLUS | +1 | Expanding | Parallel search OR creation |

### ❌ FORBIDDEN Anti-Patterns

```
"Let me first search for the files..." → search → then split
"I'll check what exists..." → read → then split  
Any grep/find/read BEFORE spawning subagents
```

### ✅ CORRECT Pattern

```
[spawn Task 1] [spawn Task 2] [spawn Task 3] → each searches internally
Subagents are XOR-independent: no shared pre-search state
Each stream discovers its own context autonomously
```

## nbb SEXP Enforcement

### Enforcer Script

Create `.ruler/trifurcation-enforcer.cljs`:

```clojure
(ns ruler.trifurcation-enforcer
  "Idempotent enforcement: NEVER read/grep/find BEFORE spawning 3 subagents.
   SplitMixTernary XOR-independence requires autonomous context discovery."
  (:require [clojure.string :as str]))

;; SplitMixTernary Constants (GF(3) field operations)
(def GOLDEN 0x9e37