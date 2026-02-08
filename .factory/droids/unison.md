---
name: unison
description: Unison language - content-addressed functional programming with abilities for effects, distributed computing, and structural types. Use for pure functional code, effect management, distributed systems, and refactoring-safe codebases.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Unison

Content-addressed functional programming language with first-class effects.

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Content-addressed** | Code identified by hash, not name - renames are free |
| **Abilities** | Algebraic effects for IO, Exception, Random, Remote |
| **Structural types** | Types with same structure are identical |
| **UCM** | Unison Codebase Manager - REPL + version control |

## UCM Commands

```bash
# Start UCM
ucm

# Start with specific project
ucm -p myproject/main

# Run compiled program
ucm run.compiled program.uc

# Create codebase at path
ucm -C ./my-codebase
```

### Inside UCM REPL

```
# Project management
project.create myproject
switch myproject/main

# Add code from scratch file
update
add

# Run a function
run helloWorld

# Compile to executable
compile helloWorld output

# Install library from Share
lib.install @unison/http

# Find definitions
find : Text -> Nat
find map

# View definition
view List.map

# Documentation
docs List.map

# Refactoring (rename is instant!)
move.term oldName newName
```

## Syntax Quick Reference

### Functions

```unison
-- Type signature
double : Nat -> Nat
double x = x * 2

-- Multi-argument
add : Nat -> Nat -> Nat
add x y = x + y

-- Lambda
List.map (x -> x * 2) [1, 2, 3]

-- Pipeline operator
[1, 2, 3] |> List.map (x -> x * 2) |> List.filter Nat.isEven
```

### Delayed Computations (Thunks)

```unison
-- Three equivalent ways to delay
main : '{IO, Exception} ()
main = do printLine "hello"

main : '{IO, Exception} ()
main _ = printLine "hello"

main : '{IO, Exception} ()
main = '(printLine "hello")

-- Force with ! or ()
!main
main()
```

### Pattern Matching

```unison
-- Match expression
isEven num = match num with
  n | mod n 2 === 0 -> "even"
  _ -> "odd"

-- Cases shorthand
isEven = cases
  0 -> "zero"
  n | Nat.isEven n -> "even"
  _ -> "odd"

-- As-patterns with @
match Some 12 with
  opt@(Some n) -> "opt binds whole value"
  None -> "none"
```

### Ty