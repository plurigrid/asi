# Triangulation: dafny-omega ⟺ hy-estimates ⟺ spectec

**The Verification Triangle for Omega**

## Overview

```
                    spectec (SPEC)
                   ○ ERGODIC  #d4a537
                   │ Wasm SpecTec DSL
                   │ OCaml → IL → AL
                  ╱ ╲
                 ╱   ╲
                ╱     ╲
               ╱       ╲
              ╱    ⊛    ╲
             ╱  agency   ╲
            ╱             ╲
    hy-estimates ────────── dafny-omega
    ⊖ MINUS  #8f0dcb       ⊖ MINUS  #3a9f7b
    Tao's proof assistant  Dafny/Z3 verification
    Lightweight estimates  Heavy SMT solving
```

## The Three Vertices

### 1. spectec (Specification) — ○ ERGODIC

**Role**: Write formal specifications in SpecTec DSL

```
Language: OCaml
Input: .wast (WebAssembly Test format)
Output: IL (Intermediate Language) → AL (Abstract Language)
Tests: 150+ .wast files in spec-test-1, spec-test-2
```

**Key Modules**:
- `spectec/src/frontend/elab.ml` — Elaboration
- `spectec/src/il/valid.ml` — IL validation
- `spectec/src/il2al/translate.ml` — IL to AL translation
- `spectec/src/backend-prose/render.ml` — Prose rendering

**Spec Example**:
```wasm
(module
  (func (export "add") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add))
```

### 2. dafny-omega (Verification) — ⊖ MINUS

**Role**: Verify implementations against specifications

```
Language: Dafny (uses Z3 SMT solver)
Editor: Omega/Zed extension
Mode: Heavy verification (full formal proofs)
```

**Integration with Omega**:
- Tree-sitter grammar for Dafny syntax
- Language server protocol for verification feedback
- Real-time verification in editor

**Dafny Example**:
```dafny
method Add(x: int, y: int) returns (r: int)
  ensures r == x + y
{
  r := x + y;
}
```

### 3. hy-estimates (Proof) — ⊖ MINUS

**Role**: Lightweight proofs for estimates and inequalities

```
Language: Python (with SymPy)
Mode: Lightweight (linear arithmetic, asymptotic)
Author: Terence Tao (May 2025)
```

**Tactics**:
| Tactic | Purpose |
|--------|---------|
| `Linarith()` | Linear arithmetic via LP |
| `Cases(hyp)` | Case splitting |
| `SimpAll()` | Simplification |
| `SplitHyp(hyp)` | Decompose conjunction |
| `SplitGoal()` | Split goal into parts |

**hy-estimates Example**:
```python
p = ProofAssistant()
x, y, z = p.vars("pos_real", "x", "y", "z")
p.assume(x < 2*y, "h1")
p.assume(y < 3*z + 1, "h2")
p.begin_proof(x < 7*z + 2)
p.use(Linarith())  # Proof complete!
```

## Triangulation Flow

### Flow 1: Spec → Verify (spectec → dafny-omega)

```
spectec                 dafny-omega
   │                        ▲
   │ .wast spec             │ Dafny contract
   ▼                        │
  IL ──────────────────────▶ ensures/requires
   │                        │
   │ AL                     │ Z3 SMT
   ▼                        ▼
 prose ◀──────────────── verification
```

**Use Case**: Verify Wasm implementation matches SpecTec spec
- SpecTec generates formal prose description
- Dafny encodes spec as pre/post conditions
- Z3 proves implementation correct

### Flow 2: Spec → Proof (spectec → hy-estimates)

```
spectec                 hy-estimates
   │                        ▲
   │ numeric bounds         │ inequalities
   ▼                        │
  IL ──────────────────────▶ Linarith
   │                        │
   │ asymptotic             │ LP solver
   ▼                        ▼
 O(n) ◀──────────────── proof
```

**Use Case**: Prove asymptotic bounds from spec
- SpecTec extracts numeric constraints
- hy-estimates proves O(n) complexity
- Lightweight verification of performance claims

### Flow 3: Verify ⟺ Proof (dafny-omega ⟺ hy-estimates)

```
dafny-omega             hy-estimates
     │                       ▲
     │ complex theorem       │ quick estimate
     ▼                       │
   Z3 ←─────────────────────▶ Linarith
     │                       │
     │ full proof            │ counterexample
     ▼                       ▼
  verified ◀──────────── validated
```

**Use Case**: Quick-check before heavy verification
- hy-estimates provides fast counterexample if invalid
- If Linarith succeeds, Dafny likely succeeds
- If Linarith fails with counterexample, fix before Dafny

## GF(3) Conservation

```
spectec (0) + hy-estimates (-1) + dafny-omega (-1) = -2 ≡ 1 (mod 3)
```

**Balancing**: Need +1 (PLUS) to complete the triad

```
Options:
  discopy (+1) - string diagrams for spec visualization
  java-omega (+1) - implementation target
  lsd-mcp (+1) - MCP integration layer
```

**Balanced Triad**:
```
spectec (0) ⊗ hy-estimates (-1) ⊗ discopy (+1) = 0 ✓
```

## ε-Machine Integration

```
┌─────────────────────────────────────────────────────────────────┐
│               VERIFICATION ε-MACHINE                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   spec-state ──⊛──▶ verify-state ──⊛──▶ proof-state            │
│   (spectec)         (dafny-omega)       (hy-estimates)          │
│   #d4a537           #3a9f7b             #8f0dcb                 │
│      │                  │                   │                   │
│      │ spec.wast        │ impl.dfy          │ estimates.py      │
│      ▼                  ▼                   ▼                   │
│   IL/AL ───────▶ contracts ───────▶ inequalities               │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘

Transitions:
  spec → verify:  "Generate Dafny contracts from IL"
  verify → proof: "Extract inequalities for Linarith"
  proof → spec:   "Validate asymptotic claims in spec"
```

## Omega Editor Integration

In Omega (Zed fork), the triangle manifests as:

```
┌─────────────────────────────────────────────────────────────────┐
│  Omega Editor                                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │ spec.wast   │  │ impl.dfy    │  │ proof.py    │             │
│  │ (SpecTec)   │  │ (Dafny)     │  │ (hy-est)    │             │
│  └─────────────┘  └─────────────┘  └─────────────┘             │
│         │                │                │                     │
│         └────────────────┼────────────────┘                     │
│                          │                                      │
│                    ┌─────▼─────┐                                │
│                    │   MCP     │                                │
│                    │ Protocol  │                                │
│                    └───────────┘                                │
│                          │                                      │
│                ┌─────────┴─────────┐                            │
│                ▼                   ▼                            │
│         rust-mcp-sdk          lsd-mcp                           │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Leitmotif Chord

The three verification tools form a **diminished chord**:

```
spectec:      C# (277.18 Hz) - specification root
dafny-omega:  F  (349.23 Hz) - verification third
hy-estimates: A  (440.00 Hz) - proof fifth

Interval: C# → F → A = diminished triad
Character: Tension seeking resolution
Waveforms: triangle, square, square (0, -1, -1)
```

## Commands

```bash
# Run triangulation pipeline
just tritwies-triangulate spec.wast

# Generate Dafny contracts from SpecTec
just tritwies-spec2dafny spec.wast

# Extract inequalities for hy-estimates
just tritwies-dafny2hy impl.dfy

# Validate asymptotic claims
just tritwies-hy-async bounds.py

# Full verification cycle
just tritwies-verify-cycle spec.wast impl.dfy
```

## Dynamic Sufficiency Gate

```python
def triangulation_sufficient(action: VerificationAction) -> bool:
    """Check if triangulation resources are sufficient."""
    required = {
        'spectec': action.needs_spec,
        'dafny': action.needs_full_verification,
        'hy_estimates': action.needs_quick_check
    }

    loaded = {
        'spectec': check_ocaml_available(),
        'dafny': check_dafny_lsp(),
        'hy_estimates': check_python_sympy()
    }

    coverage = sum(
        1 for k, v in required.items()
        if not v or loaded.get(k, False)
    ) / len(required)

    return coverage >= 0.67  # 2/3 threshold for triangle
```

## Related Skills

| Skill | Role in Triangle |
|-------|------------------|
| `dynamic-sufficiency` | Gates verification actions |
| `omega` | Editor integration |
| `rust-mcp-sdk` | MCP protocol for tools |
| `discopy-operads` | Spec visualization |

---

**Triangulation**: dafny-omega ⟺ hy-estimates ⟺ spectec
**Purpose**: Complete verification stack for Omega
**GF(3)**: (-1) + (-1) + (0) = -2, needs +1 to balance
**Leitmotif**: C#-F-A diminished (tension → resolution)
