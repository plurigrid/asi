---
name: little-schemer
description: Little Schemer Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Little Schemer Skill

> *"The Law of Car: The primitive car is defined only for non-empty lists."*
> — Friedman & Felleisen

The Friedman/Felleisen pedagogical tradition: learn by asking questions, build understanding through recursion.

## Overview

The "Little" book series by Daniel P. Friedman and collaborators teaches programming through Socratic dialogue—questions and answers that build understanding layer by layer, like peeling an onion.

## The Books

### The Little LISPer (1974, 1986, 1989) [MINUS]
**Authors**: Daniel P. Friedman, Matthias Felleisen
**Focus**: Original LISP foundations

The precursor—introduced the Q&A pedagogical style.

### The Little Schemer (1995) [PLUS]
**Authors**: Daniel P. Friedman, Matthias Felleisen
**Foreword**: Gerald Jay Sussman
**Focus**: Recursive thinking and the nature of computation

Ten Commandments + Five Laws:
1. **Car**: Only defined for non-empty lists
2. **Cdr**: Only defined for non-empty lists  
3. **Cons**: Takes two arguments, second must be list
4. **Null?**: Only defined for lists
5. **Eq?**: Takes two non-numeric atoms

Key concepts: `atom?`, `lat?`, recursion, `cond`, the Y combinator

### The Seasoned Schemer (1995) [ERGODIC]
**Authors**: Daniel P. Friedman, Matthias Felleisen
**Focus**: Continuations, state, and the nature of computation

Nineteen Commandments extending the original ten:
- **set!** and mutation
- **letcc** (call/cc)
- **letrec** for local recursion
- Collectors and continuation-passing style

Key concepts: `letcc`, `try`, collectors, the `Y!` combinator

### The Reasoned Schemer (2005, 2018) [PLUS]
**Authors**: Daniel P. Friedman, William E. Byrd, Oleg Kiselyov
**Focus**: Logic programming in Scheme (miniKanren)

Introduces relational programming:
- `run`, `fresh`, `conde`, `==`
- Unification and search
- Relations vs functions

Key concepts: miniKanren, `defrel`, `appendo`, relational arithmetic

### A Little Java, A Few Patterns (1998) [MINUS]
**Authors**: Matthias Felleisen, Daniel P. F