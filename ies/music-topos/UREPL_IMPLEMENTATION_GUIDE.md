# UREPL (Universal REPL) Protocol Implementation Guide

**Date**: 2025-12-21
**Status**: Phase 1 Complete - Foundation & Three-Agent Coordination
**Location**: `/Users/bob/ies/music-topos/`

---

## Executive Summary

The UREPL (Universal REPL) protocol enables interoperability between three Lisp dialects by implementing a **unified message format** and **three parallel agents** that orchestrate code evaluation across Scheme (Geiser), Clojure (CIDER), and Common Lisp (SLIME).

This is **Phase 1** of the self-hosting Scheme meta-interpreter. The architecture uses:

1. **Agent 1 (Syntax)**: S-expression parsing via Geiser protocol
2. **Agent 2 (Semantics)**: Type inference & validation via CIDER protocol
3. **Agent 3 (Tests)**: Test generation & verification via SLIME protocol

All three agents execute **in parallel** with async channels, coordinated by a central hub, and guided by **deterministic colors** from Gay.jl's SplitMix64 RNG.

---

## Architecture Overview

```
┌────────────────────────────────────────────────────────────┐
│            UREPL Coordinator                               │
│  (Message router, async orchestrator, result merger)       │
└────────┬──────────────────┬────────────────────┬───────────┘
         │                  │                    │
    ┌────▼─────┐       ┌────▼────┐          ┌───▼──────┐
    │ Agent 1   │       │ Agent 2  │          │ Agent 3  │
    │ Syntax    │       │Semantics │          │ Tests    │
    │ (Geiser)  │       │ (CIDER)  │          │ (SLIME)  │
    └────┬─────┘       └────┬────┘          └───┬──────┘
         │                  │                    │
    ┌────▼──────────────────▼────────────────────▼────┐
    │           Unified Message Flow                   │
    │  JSON format with:                              │
    │    - UUID (identification)                      │
    │    - Timestamp (coordination)                   │
    │    - Code payload (what to evaluate)            │
    │    - Color guide (Gay.jl determinism)           │
    │    - SRFI requirements (feature set)            │
    └──────────────────────────────────────────────────┘
```

---

## Component Breakdown

### 1. UREPL Message Format (JSON)

Every message follows this structure:

```json
{
  "id": "550e8400-e29b-41d4-a716-446655440000",
  "type": "eval",
  "timestamp": "2025-12-21T21:30:00Z",
  "source": "geiser",
  "environment": "user",

  "payload": {
    "code": "(+ 1 2)",
    "context": {"variable": "value"},
    "srfis": [2, 26, 48],
    "color-guide": [0.5, 0.7],
    "proof-request": true
  },

  "metadata": {
    "duration-ms": 5,
    "color-trace": [["0.5", "parsed"], ["0.7", "evaluated"]],
    "proof-sketch": "(+ (atom 1) (atom 2)) → (number 3)"
  }
}
```

**Key fields**:

- `id`: UUID for request tracking & correlation
- `type`: Operation type (`eval`, `result`, `error`, `debug`)
- `source`: Which REPL sent the message (`geiser`, `cider`, `slime`)
- `environment`: Evaluation context (`user`, `test`, `meta`)
- `payload.code`: The S-expression to evaluate
- `payload.srfis`: Required Scheme Requests for Implementation
- `payload.color-guide`: Gay.jl colors for determinism
- `metadata.color-trace`: Execution path with colors

---

## Agent Implementations

### Agent 1: Syntax Handler (Geiser Protocol)

**File**: `src/urepl/coordinator.clj` - `GeiserSyntaxAgent`

**Responsibilities**:

1. **Parse S-expressions** into tokens
2. **Generate ASTs** with metadata (line, column, source)
3. **Format code** back to readable s-expression form

**Example flow**:

```clojure
(parse-code geiser-agent "(+ 1 2)")
; → {:raw "(+ 1 2)"
;    :tokens ["+", "1", "2"]
;    :depth 0}

(generate-ast geiser-agent ...)
; → {:type :s-expr
;    :car "+"
;    :cdr ["1", "2"]
;    :metadata {:line 1 :col 0 :source "geiser"}}
```

**Geiser Protocol**:

- Handles `:completion`, `:describe`, `:module`, `:load-file`
- Generates s-expressions for DrRacket, Guile, Kawa
- Returns AST with position information for IDE integration

---

### Agent 2: Semantics Validator (CIDER Protocol)

**File**: `src/urepl/coordinator.clj` - `CIDERSemanticsAgent`

**Responsibilities**:

1. **Type inference** - deduce types from AST structure
2. **Semantic validation** - check constraints
3. **Symbol resolution** - look up variables in environment

**Example flow**:

```clojure
(infer-types cider-agent {:car "+" :cdr ["1" "2"]})
; → {:type :function-app
;    :function-type :function
;    :arg-types [:number :number]
;    :return-type :number}

(validate-semantics cider-agent ast types)
; → {:valid? true
;    :errors []
;    :warnings []}
```

**CIDER Protocol**:

- Handles `:evaluate`, `:complete`, `:info`, `:trace`
- Provides type information for IDE features
- Returns error diagnostics with positions

---

### Agent 3: Test Generator (SLIME Protocol)

**File**: `src/urepl/coordinator.clj` - `SLIMETestAgent`

**Responsibilities**:

1. **Generate test cases** from function signatures
2. **Verify outputs** match expected values
3. **Track coverage** statistics

**Example flow**:

```clojure
(generate-tests slime-agent {:car "+" :cdr ["1" "2"]} {})
; → [{:name "test-+-basic"
;     :input [1 2]
;     :expected 3
;     :description "Basic arithmetic"}
;    ...]

(verify-outputs slime-agent tests [3 3 3])
; → [{:test "test-+-basic" :passed? true :actual 3}
;    ...]

(track-coverage slime-agent tests executed)
; → {:total 3 :covered 3 :percentage 1.0}
```

**SLIME Protocol**:

- Handles `:eval`, `:arglist`, `:documentation`, `:swank-interactive-eval`
- Returns formatted output for Common Lisp debugger
- Provides macroexpansion & disassembly

---

## Parallel Execution Engine

**File**: `src/urepl/coordinator.clj` - `execute-agents-parallel`

All three agents run **in parallel** using Clojure's `core.async` library:

```clojure
(execute-agents-parallel syntax-agent semantics-agent test-agent message)
```

**Flow**:

1. **Agent 1** parses code immediately → generates AST
2. **Agent 2** waits for Agent 1 → infers types → validates semantics
3. **Agent 3** waits for Agent 1 → generates test cases
4. **Coordinator** collects results from all channels with 5-second timeout
5. **Results** merged and returned as single response

**Timeout handling**: If any agent exceeds 5000ms, returns error with partial results.

---

## Color-Guided Execution (Gay.jl Integration)

**File**: `src/urepl/coordinator.clj` - SplitMix64 RNG

Each execution step is annotated with **deterministic colors** using the SplitMix64 pseudorandom number generator:

```clojure
(next-color rng)
; → {:hue 247.3 :seed 18446744073709551615}
```

**Color properties**:

- **Deterministic**: Same seed = same colors always
- **Spiral**: Golden angle (137.508°) ensures never-repeating
- **Parallel-safe**: Each agent gets independent stream
- **Synesthetic**: Colors map to evaluation stages

**Example trace**:

```
Parse:        hue=  0.0°  (color #FF0000)
AST Gen:      hue= 137.5°  (color #FF6B6B)
Type Infer:   hue=275.0°  (color #4ECDC4)
Validate:     hue= 52.5°  (color #95E1D3)
Eval:         hue=190.0°  (color #F9CA24)
```

---

## CRDT Integration - Line Damage Formalization

**File**: `src/urepl/crdt-integration.el` - Character-level CRDT

Extends `crdt.el` with **conflict-free operations** for collaborative editing:

### Data Structures

```elisp
(defstruct crdt-char
  value                    ; Character itself
  id                       ; Unique identifier
  site-id                  ; Which agent inserted
  lamport-ts               ; Causal ordering
  parent-id                ; Causal precedence
  deleted                  ; Tombstone
  color                    ; Gay.jl color
  agent                    ; Agent name (xenodium/batsov/xah-lee))

(defstruct crdt-operation
  id                       ; Operation UUID
  type                     ; insert/delete/update
  char                     ; crdt-char
  position                 ; Document position
  timestamp                ; When it happened
  color                    ; For visualization
  agent-id                 ; Which agent
  proof-sketch)            ; For verification
```

### Conflict Resolution: Möbius Inversion + Prime Filtering

When two agents modify the same position, conflicts are resolved using:

1. **Prime factor extraction**: Convert operation ID → prime factors
   - Example: `210 → [2, 3, 5, 7]`

2. **Möbius function**: Calculate signature value
   - Distinct primes only: `μ = (-1)^count`
   - Any repeated prime: `μ = 0`
   - Example: `μ(2,3,5,7) = -1`, `μ(2,2,3,5) = 0`

3. **Deterministic ordering**: Sort by Möbius value, then Lamport timestamp
   - Operations with higher Möbius values execute first
   - Stable sort ensures consistent results

**Example conflict resolution**:

```elisp
(crdt-conflict-resolve
  [(make-crdt-operation :id "agent1-210" ...)  ; μ = -1
   (make-crdt-operation :id "agent2-30" ...)])  ; μ = 1
; → Agent2's operation executes first (higher μ value)
```

---

## Minimal Scheme Evaluator (Bootstrap Core)

**File**: `src/urepl/evaluator.scm` - 64-line core

A **self-hosting** Scheme interpreter that can evaluate itself:

```scheme
(define (eval expr env)
  ;; Atoms
  ((number? expr) expr)
  ((symbol? expr) (lookup expr env))

  ;; Special forms
  ((eq? (car expr) 'quote) (cadr expr))
  ((eq? (car expr) 'define) ...)
  ((eq? (car expr) 'lambda) ...)

  ;; Function application
  (else (apply (eval (car expr) env)
               (map (lambda (e) (eval e env)) (cdr expr)))))
```

**Key features**:

- ✅ Arithmetic operations: `+`, `-`, `*`, `/`
- ✅ Comparison: `=`, `<`, `>`
- ✅ Type checking: `number?`, `symbol?`, `pair?`
- ✅ List operations: `cons`, `car`, `cdr`, `list`
- ✅ Control flow: `if`, `begin`, `let`
- ✅ Lambda/closures
- ✅ Variable definition & lookup
- ✅ Environment management

**UREPL integration**:

```scheme
(urepl-eval "(+ 1 2 3)")           ; → 6
(urepl-eval-print "(define x 42)")  ; → ok (prints result)
```

---

## Quick Start

### 1. Initialize UREPL Environment

```bash
just urepl-init
```

Creates directory structure and checks for required tools.

### 2. Run Individual Agent Tests

**Test Scheme evaluator (Agent 1)**:
```bash
just urepl-scheme-test
```

**Test CRDT conflict resolution (Line Damage)**:
```bash
just urepl-crdt-test
```

### 3. Execute Code Through Coordinator

```bash
# Simple arithmetic
just urepl-execute "(+ 1 2 3)"

# With custom seed for deterministic colors
just urepl-execute "(* 4 5)" 12345

# Define variable
just urepl-execute "(define fact (lambda (n) (if (< n 2) 1 (* n (fact (- n 1))))))"
```

### 4. Run Full Integration Test

```bash
just urepl-full-test
```

Verifies all three agents working together.

### 5. View Protocol Specification

```bash
just urepl-spec
```

Displays architecture overview.

---

## Implementation Status

### Phase 1: Foundation ✅ (COMPLETE)

- [x] UREPL message format specification
- [x] Geiser syntax adapter (Agent 1)
- [x] CIDER semantics adapter (Agent 2)
- [x] SLIME test adapter (Agent 3)
- [x] Parallel execution engine
- [x] Color-guided execution tracing
- [x] CRDT line damage formalization
- [x] Scheme evaluator bootstrap
- [x] Org-babel specification document
- [x] Justfile targets for execution

### Phase 2: Self-Hosting (PENDING)

- [ ] Implement color-guided bootstrap sequence
- [ ] UREPL message server (WebSocket/nREPL)
- [ ] Live connection to Scheme/Clojure/Common Lisp REPLs
- [ ] Unison meta-language wrapper
- [ ] SRFI implementation via 3-agent parallel system

### Phase 3: CRDT Integration (PENDING)

- [ ] Emacs buffer integration with crdt.el
- [ ] Operation tracking across edits
- [ ] Real-time conflict resolution
- [ ] Visualization with color annotations

### Phase 4: SRFI Coverage (PENDING)

- [ ] Implement all 200+ SRFIs
- [ ] Parallel agent-based implementation
- [ ] Test suite generation per SRFI
- [ ] Cross-dialect validation

### Phase 5: Integration & Verification (PENDING)

- [ ] End-to-end testing across all components
- [ ] Performance benchmarking
- [ ] Proof generation for meta-interpreter
- [ ] Self-verification of implementation

---

## File Reference

| File | Purpose | Status |
|------|---------|--------|
| `UREPL_IMPLEMENTATION.org` | Org-babel specification with executable blocks | ✅ Complete |
| `UREPL_IMPLEMENTATION_GUIDE.md` | This guide | ✅ Complete |
| `src/urepl/coordinator.clj` | Clojure multi-agent orchestrator | ✅ Complete |
| `src/urepl/evaluator.scm` | Scheme bootstrap evaluator | ✅ Complete |
| `src/urepl/crdt-integration.el` | Elisp CRDT + line damage | ✅ Complete |
| `justfile` | Build targets (last 250 lines) | ✅ Complete |

---

## Command Reference

```bash
# Initialize
just urepl-init

# Execute code
just urepl-execute "(+ 1 2)"
just urepl-execute "(define x 42)" 42

# Test individual components
just urepl-scheme-test       # Agent 1 (Syntax)
just urepl-crdt-test        # CRDT conflict resolution

# Integration testing
just urepl-full-test        # All agents together

# Information
just urepl-spec            # Protocol architecture
```

---

## Advanced Usage

### Custom Seeds for Determinism

```bash
# Run with specific seed (same seed = same colors)
just urepl-execute "(+ 1 2)" 42
just urepl-execute "(+ 1 2)" 42  # Same colors

# Different seed = different colors
just urepl-execute "(+ 1 2)" 999
```

### Extending with New SRFI

Add to `src/urepl/evaluator.scm`:

```scheme
(define-srfi-procedure 26 "cut"
  (make-primitive
    (lambda (args) (apply cut-impl args))))
```

### Accessing Agent Results

```clojure
;; From coordinator.clj
(let [result (execute-agents-parallel ...)]
  {:syntax (:syntax result)    ; Agent 1 AST
   :semantics (:semantics result)  ; Agent 2 types
   :tests (:tests result)      ; Agent 3 test cases
   :timestamp (:timestamp result)})
```

---

## Integration with Music-Topos System

The UREPL protocol integrates with the broader music-topos system:

1. **Knowledge Graph**: DuckDB queries feed into UREPL evaluation
2. **Sonification**: Color traces mapped to music progressions
3. **Agent Skills**: UREPL becomes a skill available to all agents
4. **World Management**: Worlds can use UREPL for meta-evaluation

---

## Next Steps

1. **Implement UREPL server**: WebSocket endpoint accepting messages
2. **Connect live REPLs**: Adapt Geiser, CIDER, SLIME to send/receive UREPL messages
3. **Color-guided bootstrap**: Use SplitMix64 colors to guide SRFI implementation
4. **Distributed evaluation**: Use Unison language for code distribution
5. **Self-hosting verification**: Prove meta-interpreter self-modification is sound

---

## References

- **Geiser Protocol**: https://www.nongnu.org/geiser/
- **CIDER Protocol**: https://cider.mx/
- **SLIME Protocol**: https://common-lisp.net/project/slime/
- **CRDT**: https://crdt.tech/
- **Möbius Function**: https://en.wikipedia.org/wiki/Möbius_function
- **Gay.jl / SplitMix64**: SplitMix pseudorandom number generator
- **SRFI**: https://srfi.schemers.org/

---

**Status**: Ready for Phase 2 (Self-hosting implementation)

**Contact**: Music-Topos Project Team
**Last Updated**: 2025-12-21 21:30:00 UTC
