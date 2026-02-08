---
name: lambda-calculus
description: Lambda Calculus Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# lambda-calculus Skill


> *"Three rules. Infinite computation. The foundation of all functional programming."*

## Overview

**Lambda Calculus** implements Church's lambda calculus, the mathematical foundation of functional programming. Variables, abstraction, and application - that's all you need.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | +1 (PLUS) |
| Role | GENERATOR |
| Function | Generates terms and reductions |

## The Three Rules

```
┌─────────────────────────────────────────────────────────────────┐
│                    LAMBDA CALCULUS SYNTAX                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Term ::= x           Variable                                  │
│        |  λx. Term    Abstraction (function definition)        │
│        |  Term Term   Application (function call)               │
│                                                                 │
│  That's it. Everything else is encoded.                        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## β-Reduction

```
The only computation rule:

(λx. M) N  →β  M[x := N]

"Apply function λx.M to argument N by substituting N for x in M"

Example:
(λx. x x) (λy. y)
→β (λy. y) (λy. y)
→β λy. y

```

## Church Encodings

```haskell
-- Booleans
true  = λt. λf. t
false = λt. λf. f
if    = λb. λt. λf. b t f

-- Numbers (Church numerals)
zero  = λf. λx. x
one   = λf. λx. f x
two   = λf. λx. f (f x)
three = λf. λx. f (f (f x))

succ  = λn. λf. λx. f (n f x)
plus  = λm. λn. λf. λx. m f (n f x)
mult  = λm. λn. λf. m (n f)

-- Pairs
pair  = λx. λy. λf. f x y
fst   = λp. p (λx. λy. x)
snd   = λp. p (λx. λy. y)

-- Lists
nil   = λc. λn. n
cons  = λh. λt. λc. λn. c h (t c n)
```

## Fixed Point Combinator

```haskell
-- Y combinator: enables recursion without recursion!
Y = λf. (