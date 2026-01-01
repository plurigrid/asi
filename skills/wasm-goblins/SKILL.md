---
name: wasm-goblins
description: Goblins ↔ WASM runtime interactions across verified runtimes. Capability-secure
  distributed actors meeting sandboxed execution.
source: spritely/goblins + hoot + verified-wasm-ecosystem
license: Apache-2.0
trit: 0
gf3_conserved: true
metadata:
  interface_ports:
  - Related Skills
---
# WASM Goblins (0)

> Capability-secure actors meet verified WASM sandboxes

**Trit**: 0 (ERGODIC - mediates capabilities ↔ sandboxes)

## Verified WASM Runtime Matrix

| Runtime | Verification | Execution | Goblins Interaction |
|---------|--------------|-----------|---------------------|
| **Wasmtime** | Cranelift formal semantics, Iris-Wasm | JIT/AOT | Host function imports |
| **WAMR** | WAVEN memory virtualization | Interpreter/AOT | SGX enclave isolation |
| **Wasmer** | WASIX syscall layer | Singlepass/Cranelift/LLVM | Full POSIX + TTY |
| **WasmEdge** | CNCF certified | Interpreter/AOT | Kubernetes integration |
| **wasm3** | Minimal TCB interpreter | Interpreter only | Embedded/IoT |
| **Hoot** | Scheme semantics preservation | Guile interpreter | Native Goblins bridge |

## Goblins → WASM Interaction Patterns

### 1. Actor as WASM Module

```scheme
;; Goblins actor that wraps a WASM module
(define (^wasm-actor bcom wasm-bytes)
  (define instance (wasm-instantiate wasm-bytes))
  
  (define (call method . args)
    (wasm-invoke instance method args))
  
  (methods
   [call call]
   [memory (lambda () (wasm-memory instance))]))
```

### 2. WASM Module as Actor

```scheme
;; WASM module exporting Goblins-compatible interface
;; Compiled from Hoot
(define-module (wasm-counter)
  #:export (spawn-counter))

(define (spawn-counter initial)
  (let ([count initial])
    (lambda (msg)
      (match msg
        ['inc (set! count (+ count 1))]
        ['get count]))))
```

### 3. Capability Passing via WASM Handles

```
┌─────────────────────────────────────────────────────────────┐
│                     Goblins Vat                             │
│  ┌─────────┐     ┌─────────┐     ┌─────────┐               │
│  │ Actor A │────→│ WASM    │────→│ Actor B │               │
│  │ (Scheme)│ cap │ Module  │ cap │ (Scheme)│               │
│  └─────────┘     └─────────┘     └─────────┘               │
│       ↑              ↑               ↑                      │
│       └──────────────┴───────────────┘                      │
│              OCapN / CapTP                                  │
└─────────────────────────────────────────────────────────────┘
```

## WASM Syscall Categories

### WASI (Base - All Runtimes)

| Syscall | Goblins Mapping | Trit |
|---------|-----------------|------|
| `fd_read` | File capability | -1 |
| `fd_write` | File capability | +1 |
| `clock_time_get` | Ambient authority | 0 |
| `random_get` | Entropy source | 0 |
| `proc_exit` | Vat termination | -1 |

### WASIX (Wasmer Extended)

| Syscall | Goblins Mapping | Trit |
|---------|-----------------|------|
| `thread_spawn` | Actor spawn | +1 |
| `proc_fork` | Vat fork | +1 |
| `sock_connect` | Network capability | 0 |
| `tty_get/set` | Console capability | 0 |
| `futex_*` | Synchronization | 0 |

### WAVEN (SGX Memory Virtualization)

| Feature | Goblins Mapping | Trit |
|---------|-----------------|------|
| Page-level sharing | Shared actor state | 0 |
| Dual page tables | Read/write capabilities | ±1 |
| Exception pages | Fault isolation | -1 |

## Verified Semantics

### Iris-Wasm (Coq Mechanized)

```
Wasm 1.0 Spec ──→ Coq Mechanization ──→ Iris Separation Logic
                                              ↓
                              Robust Capability Safety Proofs
```

**Key properties verified:**
- Memory isolation between modules
- Control flow integrity
- Type safety preservation
- Capability encapsulation (MSWasm extension)

### Cranelift Verification

```
CLIF IR ──→ VeriWasm ──→ Machine Code
              ↓
     SFI guarantee preservation
     Constant-time compilation (ct-wasm)
```

## Hoot Bridge (Native Goblins ↔ WASM)

```scheme
;; Compile Goblins actor to WASM
(use-modules (hoot compile) (goblins))

(define (^portable-actor bcom)
  (lambda (msg)
    (match msg
      ['ping 'pong]
      [('echo x) x])))

;; Compile to WASM with preserved semantics
(compile-actor ^portable-actor
  #:output "actor.wasm"
  #:tail-calls #t        ; Wasm tail-call proposal
  #:gc #t)               ; Wasm GC proposal
```

### Hoot WASM Features

| Feature | WASM Proposal | Status |
|---------|---------------|--------|
| Tail calls | tail-call | Stage 4 ✓ |
| GC | gc | Stage 4 ✓ |
| Continuations | stack-switching | Stage 2 |
| Exception handling | exception-handling | Stage 4 ✓ |
| Threads | threads | Stage 4 ✓ |

## Runtime Selection Matrix

```
Use Case                          Runtime          Reason
─────────────────────────────────────────────────────────────
Browser + Goblins                 Hoot             Native Scheme semantics
Server + Multi-tenant             Wasmtime         Verified + fast
TEE / Enclave                     WAMR + WAVEN     SGX memory virtualization
Edge / IoT                        wasm3            Minimal footprint
Full POSIX / Terminal             Wasmer + WASIX   TTY + fork + threads
Kubernetes / Cloud Native         WasmEdge         CNCF ecosystem
```

## GF(3) Triad: WASM Runtime Layer

```
Hoot (+1)      ⊗ Goblins (0)    ⊗ WAVEN (-1)     = 0 ✓
generative       orchestration    verification
Scheme→WASM      actor dispatch   memory isolation
```

## Interaction Examples

### 1. Nickel Contract → WASM Module

```scheme
;; Load Nickel-validated config into WASM actor
(define (^config-actor bcom nickel-json)
  (define config (json->scheme nickel-json))
  (define wasm (compile-config-handler config))
  (define instance (wasm-instantiate wasm))
  
  (lambda (key)
    (wasm-invoke instance 'get key)))
```

### 2. Juvix Intent → WASM Execution

```scheme
;; Execute Juvix-compiled intent in sandboxed WASM
(define (^intent-executor bcom intent-wasm)
  (define instance 
    (wasm-instantiate intent-wasm
      #:imports `((geb . ,geb-morphism-table))))
  
  (lambda (resources)
    (wasm-invoke instance 'execute resources)))
```

### 3. WASIX Terminal → Goblins REPL

```scheme
;; REPL actor with terminal capabilities
(define (^repl-actor bcom tty-cap)
  (define (read-eval-print)
    (define input (<- tty-cap 'read-line))
    (define result (eval (read input)))
    (<- tty-cap 'write (format #f "~a\n" result))
    (read-eval-print))
  
  (methods
   [start read-eval-print]))
```

## Security Properties

| Property | Enforcement | Runtime |
|----------|-------------|---------|
| **Memory safety** | Linear memory bounds | All |
| **Control flow integrity** | Type-checked indirect calls | All |
| **Capability confinement** | Import/export attenuation | Goblins |
| **Temporal safety** | MSWasm handles | Iris-MSWasm |
| **Constant-time** | ct-wasm type system | Wasmtime |
| **Enclave isolation** | EPCM + WAVEN | WAMR |

---

## End-of-Skill Interface

## Related Skills

| Skill | Trit | Bridge |
|-------|------|--------|
| hoot | 0 | Native compiler |
| goblins | 0 | Actor system |
| guile-goblins-hoot | +1 | Unified stack |
| nickel | 0 | Config validation |
| juvix-intents | +1 | Intent compilation |
| wasix (external) | -1 | POSIX syscalls |

---

**Trit**: 0 (ERGODIC - mediates compilation ↔ execution ↔ verification)
**Key Property**: Verified sandboxes + capability discipline = compositional security
