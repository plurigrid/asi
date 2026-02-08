---
name: concatenative
description: "Forth/Factor/Joy: stack-based concatenative programming where composition replaces application."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Concatenative Programming Skill

> *"Programs are composed by concatenation. The stack is the only state."*

## Core Concept

In concatenative languages:
1. **Stack** is the implicit data structure
2. **Words** (functions) transform the stack
3. **Composition = Concatenation** — `f g` means "do f, then g"
4. **No variables** (mostly) — data flows through stack

```forth
3 4 +        \ Push 3, push 4, add → 7 on stack
dup *        \ Duplicate top, multiply → 49
```

## Why It's Strange

1. **No application** — `f(x)` becomes `x f`
2. **No variables** — use stack manipulation
3. **Point-free by default** — everything is tacit
4. **Quotations** — code as data `[ ... ]`
5. **Extreme composability** — every word combines freely

## Forth Basics

```forth
\ Comments start with backslash
3 4 +           \ → 7
10 3 /          \ → 3 (integer division)
1 2 3 + *       \ 1 * (2 + 3) = 5

\ Stack manipulation
DUP             \ a → a a
DROP            \ a b → a
SWAP            \ a b → b a
OVER            \ a b → a b a
ROT             \ a b c → b c a

\ Defining words
: SQUARE  DUP * ;
5 SQUARE        \ → 25

: CUBE  DUP DUP * * ;
3 CUBE          \ → 27
```

## Factor (Modern Forth)

```factor
! Stack effect declarations
: square ( n -- n^2 ) dup * ;
: cube ( n -- n^3 ) dup dup * * ;

! Quotations (anonymous functions)
{ 1 2 3 } [ 2 * ] map   ! → { 2 4 6 }
{ 1 2 3 4 } [ even? ] filter  ! → { 2 4 }

! Cleave combinator (apply multiple quotations)
5 [ 1 + ] [ 2 * ] bi    ! → 6 10

! Spread combinator
1 2 [ 1 + ] [ 2 * ] bi* ! → 2 4
```

## Joy (Functional Concatenative)

```joy
# No mutable state, pure functional
# Quotations are first-class
[dup *] square define
5 square                  # → 25

# Combinators
[1 2 3] [2 *] map         # → [2 4 6]
[1 2 3 4 5] 0 [+] fold    # → 15

# Recursion via Y combinator
[dup 0 = [pop 1] [dup 1 - factorial *] ifte] factorial define
5 factorial               # → 120
```

## Stack Effect Notation

```
( before -- after )

dup   ( a -- a a )
dr