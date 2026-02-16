---
name: miasm-symbolic
description: Miasm reverse engineering framework for symbolic execution, IR lifting, and binary analysis. Interoperates with blackhat-go via adversarial bisimulation games and GF(3) conservation.
source: cea-sec/miasm
license: GPL-2.0
aaif-compatible: true
mcp-version: "2025.1"
gf3-trit: 0
---

# Miasm Symbolic Execution Skill

**Status**: ✅ Production Ready  
**Source**: CEA-SEC Miasm Framework (3.8K stars)  
**Interop**: blackhat-go adversarial bisimulation games  
**GF(3)**: ERGODIC (0) - transformation/mediation role

---

## Conscious Hacker Integration Philosophy

The conscious hacker recognizes that **offensive and defensive security are dual**:

```
blackhat-go (attack chains) ←→ miasm-symbolic (program understanding)
        ↓                              ↓
   Order matters (Ungar)        State equivalence (Bisim)
        ↓                              ↓
    MINUS (-1)                    ERGODIC (0)
```

Together with a **defense verification** skill (+1), this maintains GF(3) conservation.

---

## Overview

Miasm provides:

- **16 Architectures**: x86_16/32/64, ARM, MIPS, AArch64, PPC, SH4, MSP430, MEP
- **IR Lifting**: Assembly → Intermediate Representation
- **Symbolic Execution**: Constraint solving for path exploration
- **Emulation**: JIT-based binary emulation
- **DSE**: Dynamic Symbolic Execution

## GF(3) Role Assignment

| Component | Trit | Role |
|-----------|------|------|
| Disassembly (r2/miasm) | -1 | MINUS - deconstruction |
| IR Lifting (miasm) | 0 | ERGODIC - transformation |
| Symbolic Exec (miasm) | +1 | PLUS - construction |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

---

## Adversarial Bisimulation Bridge to blackhat-go

### Attack Chain Verification

When blackhat-go executes an Ungar game attack chain, miasm can **verify semantics**:

```python
from miasm_r2_bridge import MiasmR2Bridge

# blackhat-go attack: shellcode injection
attack_chain = ["go-concurrency", "shellcode-inject", "process-hollow"]

# miasm verification: does shellcode do what attacker claims?
bridge = MiasmR2Bridge(shellcode_path, "x86_64")

# Lift to IR and symbolically execute
ir = bridge.lift_to_ir(entry_point, shellcode_bytes)
symbolic_state = bridge.symbolic_exec(ir)

# Check: does shellcode reach claimed goal state?
goal_reached = symbolic_state.check_constraint(goal_condition)
```

### Bisimulation: Semantic Equivalence

Two binaries are **bisimilar** if miasm symbolic execution shows they produce
equivalent observable states:

```python
def check_binary_bisimilar(bin1: bytes, bin2: bytes) -> bool:
    """
    Check if two binaries are behaviorally equivalent.
    Used in blackhat-go bisimulation games for defense validation.
    """
    bridge1 = MiasmR2Bridge(bin1, "x86_64")
    bridge2 = MiasmR2Bridge(bin2, "x86_64")
    
    sym1 = bridge1.symbolic_exec_full()
    sym2 = bridge2.symbolic_exec_full()
    
    # Compare final symbolic states
    return sym1.is_equivalent(sym2)
```

### Game Message Protocol

```json
{
  "type": "miasm/verify",
  "game_id": "bisim-001",
  "player": "arbiter",
  "action": {
    "operation": "symbolic_equivalence_check",
    "binary1_hash": "abc123",
    "binary2_hash": "def456"
  },
  "result": {
    "bisimilar": true,
    "constraints_matched": 42,
    "paths_explored": 1337
  },
  "trit": 0
}
```

---

## Supported Architectures

```python
from miasm.analysis.machine import Machine

ARCHITECTURES = Machine.available_machine()
# ['arml', 'armb', 'armtl', 'armtb', 'sh4', 'x86_16', 'x86_32', 'x86_64',
#  'msp430', 'mips32b', 'mips32l', 'aarch64l', 'aarch64b', 'ppc32b', 
#  'mepl', 'mepb']
```

---

## Core Capabilities

### 1. Disassembly with Gay.jl Coloring

```python
from miasm_r2_bridge import MiasmR2Bridge, GayColor

bridge = MiasmR2Bridge("/path/to/binary", "x86_64")
colors = GayColor(seed=1069)

instrs = bridge.disassemble_function(0x1000, code_bytes)
for instr in instrs:
    print(f"{instr['addr']}: {instr['mnemonic']} | {instr['color']}")
```

### 2. IR Lifting

```python
# Lift x86_64 instruction to miasm IR
ir = bridge.lift_to_ir(0x1000, shellcode)
# Result: {'addr': '0x1000', 'asm': 'MOV RAX, 0x42', 
#          'ir': [{'dst': 'RAX', 'src': '0x42'}]}
```

### 3. Symbolic Execution

```python
from miasm.ir.symbexec import SymbolicExecutionEngine
from miasm.expression.expression import ExprId, ExprInt

# Create symbolic state
symbols = {
    ExprId("RAX", 64): ExprId("RAX_init", 64),  # Symbolized
    ExprId("RBX", 64): ExprInt(0, 64),          # Concrete
}

# Execute symbolically
engine = SymbolicExecutionEngine(ir_arch, symbols)
final_state = engine.run_at(ir_cfg, entry_addr)

# Query: what value does RAX hold?
rax_expr = final_state.eval_expr(ExprId("RAX", 64))
```

### 4. Constraint Solving (with Z3)

```python
from miasm.ir.translators.z3_ir import TranslatorZ3

translator = TranslatorZ3()
z3_expr = translator.from_expr(rax_expr)

# Solve for input that makes RAX == 0x1337
import z3
solver = z3.Solver()
solver.add(z3_expr == 0x1337)
if solver.check() == z3.sat:
    model = solver.model()
    print(f"Input to reach RAX=0x1337: {model}")
```

---

## blackhat-go Interoperability

### Ungar Game: Attack Verification

```go
// blackhat-go side
game := NewUngarGame(kb)
game.AttackerMove("shellcode-inject")

// MCP message to miasm
msg := MCPMessage{
    Type: "miasm/verify_attack",
    Payload: AttackVerification{
        Technique: "shellcode-inject",
        Shellcode: shellcodeBytes,
        ClaimedBehavior: "spawns /bin/sh",
    },
}

// miasm verifies via symbolic execution
response := miasmService.Verify(msg)
if response.Verified {
    game.ArbiterVerify() // GF(3) balance maintained
}
```

### Bisimulation Game: Defense Equivalence

```go
// blackhat-go: are two defenses equivalent?
bisim := NewBisimulationGame(kb, defense1, defense2)

// Use miasm to check binary-level equivalence
miasmCheck := miasm.CheckBisimilar(defense1.Binary, defense2.Binary)

if miasmCheck.Equivalent {
    // Defender wins: defenses are observationally equivalent
    bisim.DefenderWins()
}
```

---

## Installation

```bash
# Requires pyparsing < 3 for miasm compatibility
uv venv --python 3.11 /tmp/miasm_venv
source /tmp/miasm_venv/bin/activate
uv pip install "pyparsing==2.4.7" miasm future

# Optional: Z3 for constraint solving
uv pip install z3-solver
```

---

## Three Worlds Integration

| World | Seed | miasm Role | blackhat-go Role |
|-------|------|------------|------------------|
| 🔴 ZAHN | 1069 | Verify attack semantics | Execute attack chains |
| 🟢 JULES | 69 | Check binary equivalence | Validate defenses |
| 🔵 FABRIZ | 0 | Arbiter symbolic proofs | Arbiter game state |

---

## MCP Tool Exposure

```json
{
  "tools": [
    {
      "name": "miasm_disassemble",
      "description": "Disassemble bytes with miasm",
      "parameters": {
        "arch": "x86_64",
        "bytes": "base64-encoded",
        "addr": "0x1000"
      }
    },
    {
      "name": "miasm_lift_ir",
      "description": "Lift assembly to miasm IR",
      "parameters": {
        "arch": "x86_64",
        "bytes": "base64-encoded"
      }
    },
    {
      "name": "miasm_symbolic_exec",
      "description": "Run symbolic execution",
      "parameters": {
        "ir": "ir-json",
        "symbols": {"RAX": "symbolic"}
      }
    },
    {
      "name": "miasm_check_bisimilar",
      "description": "Check if two binaries are bisimilar",
      "parameters": {
        "binary1": "base64",
        "binary2": "base64",
        "depth": 100
      }
    }
  ]
}
```

---

## Conscious Hacker Principles

1. **Understand before attack**: Use miasm to understand what code *actually does*
2. **Verify claims**: Don't trust attacker claims without symbolic verification
3. **Defense through understanding**: Bisimulation proves defense equivalence
4. **GF(3) balance**: Every attack (-1) needs understanding (0) and defense (+1)

---

## Related Skills

| Skill | Trit | Role |
|-------|------|------|
| blackhat-go | -1 | Attack chains, Ungar games |
| miasm-symbolic | 0 | IR lifting, symbolic exec |
| narya-proofs | +1 | Formal verification |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

---

## Contributors (CEA-SEC)

| Contributor | Role | Followers |
|-------------|------|-----------|
| serpilliere | Creator | 107 |
| commial (Camille Mougey) | Core dev | 286 |
| mrphrazer (Tim Blazytko) | Contributor | 521 |
| mrexodia (Duncan Ogilvie) | x64dbg creator | 3,334 |

---

## File Locations

```
~/.claude/skills/miasm-symbolic/SKILL.md    # This skill
~/iii/src/miasm_r2_bridge.py                # Bridge implementation
~/iii/r2con-integration/                     # r2con integration
```

---

*"The conscious hacker uses miasm not to attack, but to understand—and through understanding, to protect."*


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
