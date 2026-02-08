---
name: srfi
description: SRFI Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# SRFI Skill

> *"SRFIs extend the Scheme programming language. You can help."*
> — srfi.schemers.org

Scheme Requests for Implementation: portable library specifications with GF(3) categorization.

## Overview

SRFIs are community-driven specifications that extend Scheme beyond R5RS/R6RS/R7RS. Each SRFI has a unique number, status (draft/final/withdrawn), and reference implementation.

## Core SRFIs by Category

### Data Structures [MINUS: -1]

| SRFI | Name | Status | Key Exports |
|------|------|--------|-------------|
| 1 | List Library | Final | `fold`, `unfold`, `filter`, `partition` |
| 4 | Homogeneous Vectors | Final | `u8vector`, `f64vector`, typed arrays |
| 9 | Defining Record Types | Final | `define-record-type` |
| 14 | Character Sets | Final | `char-set`, `char-set-contains?` |
| 69 | Basic Hash Tables | Final | `make-hash-table`, `hash-table-ref` |
| 113 | Sets and Bags | Final | `set`, `bag`, `set-contains?` |
| 125 | Intermediate Hash Tables | Final | `hash-table-map`, comparators |
| 128 | Comparators (Reduced) | Final | `make-comparator`, `comparator-hash` |
| 133 | Vector Library | Final | `vector-map`, `vector-fold` |
| 146 | Mappings | Final | `mapping`, functional maps |
| 158 | Generators and Accumulators | Final | `make-coroutine-generator` |

### Control Flow [ERGODIC: 0]

| SRFI | Name | Status | Key Exports |
|------|------|--------|-------------|
| 2 | AND-LET* | Final | `and-let*` short-circuit binding |
| 8 | receive | Final | `receive` for multiple values |
| 11 | let-values | Final | `let-values`, `let*-values` |
| 18 | Multithreading | Final | `make-thread`, `mutex`, `condition-variable` |
| 34 | Exception Handling | Final | `guard`, `raise` |
| 39 | Parameter Objects | Final | `make-parameter`, `parameterize` |
| 45 | Primitives for Lazy Eval | Final | `delay`, `force`, `lazy` |
| 124 | Ephemerons | Final | `make-ephemeron`, weak references |
| 154 | First-Class Dynamic Extents | Final | `dynamic-extent`, delimited continuations |
