# QASM Integration Guide

## Overview

**Phase 3C Extension**: Quantum Assembly Language (OpenQASM 3.0) support for hybrid quantum-classical CRDT circuits.

Maps the 3-coloring constraint system to quantum gates:
- **RED** (positive/forward): Hadamard and unitary operations
- **BLUE** (negative/inverse): Adjoint operations (S†, T†, etc.)
- **GREEN** (neutral/identity): Measurement and verification operations

---

## Architecture

### Color-to-Gate Mapping

```rust
RED   → QuantumGate::H      // Hadamard: creates superposition
BLUE  → QuantumGate::Sdg    // S-dagger: inverse of phase gate
GREEN → QuantumGate::Id     // Identity: measurement/verification
```

### Components

**`src/qasm_integration.rs`** (P1+ component, 300 lines)
- `QuantumGate`: Single-qubit (H, S, T, RX/Y/Z) and two-qubit (CX, CY, CZ, SWAP) gates
- `HybridCircuit`: Quantum-classical hybrid circuit representation
- `QasmTransducer`: Pattern-based quantum circuit generation
- 15 comprehensive tests

---

## Usage

### Basic Circuit Generation

```rust
use fermyon_agents::*;

let mut transducer = QasmTransducer::new();

// Create a hybrid circuit
let mut circuit = HybridCircuit::new("superposition".to_string(), 2, 2);
circuit.add_gate(QuantumGate::H, vec![0]);        // Hadamard on q0
circuit.add_gate(QuantumGate::CX, vec![0, 1]);   // CNOT
circuit.add_gate(QuantumGate::Measure, vec![0]); // Measure

transducer.register_circuit(circuit);
let qasm = transducer.export_qasm("superposition").unwrap();
println!("{}", qasm);
```

### Output Example

```qasm
OPENQASM 3.0;
include "stdgates.inc";
qubit[2] q;
bit[2] c;

// superposition
h q[0];
cx q[0], q[1];
measure q[0] -> c[0];
```

### Color-Based Circuit Generation

```rust
let mut circuit = HybridCircuit::new("color_circuit".to_string(), 3, 3);

// Use color-to-gate mapping
let red_gate = QuantumGate::from_color(Color::Red);    // H
let blue_gate = QuantumGate::from_color(Color::Blue);  // Sdg
let green_gate = QuantumGate::from_color(Color::Green); // Id

circuit.add_gate(red_gate, vec![0]);
circuit.add_gate(blue_gate, vec![1]);
// Green is no-op, often removed by optimization
```

### Parameterized Circuits (Variational Ansatz)

```rust
let circuit = transducer.generate_parameterized_circuit(
    "ansatz".to_string(),
    3,     // 3 qubits
    2,     // 2 layers
);

// Circuit contains parameterized RY gates
// Format: ry(π/4) q[0]; ry(π/4) q[1]; ry(π/4) q[2];
//         cx q[0], q[1];  cx q[1], q[2];   (entanglement)
//         [repeat for layer 2]
//         measure q[0] -> c[0]; ...
```

### Circuit Optimization

```rust
let mut circuit = HybridCircuit::new("before_opt".to_string(), 2, 2);
circuit.add_gate(QuantumGate::Id, vec![0]);     // No-op
circuit.add_gate(QuantumGate::H, vec![1]);      // Real operation

transducer.register_circuit(circuit);
transducer.optimize_circuit("before_opt").unwrap();

// Identity gates removed
let opt = transducer.circuits.get("before_opt").unwrap();
assert_eq!(opt.gate_count(), 1); // Only H remains
```

### Reversibility (Quantum-Classical Hybrid)

```rust
// Create forward circuit
let mut fwd = HybridCircuit::new("forward".to_string(), 2, 2);
fwd.add_gate(QuantumGate::S, vec![0]);
fwd.add_gate(QuantumGate::H, vec![1]);

transducer.register_circuit(fwd);

// Generate inverse (S† then H†=H)
let inv_name = transducer.inverse_circuit("forward").unwrap();
let inv = transducer.circuits.get(&inv_name).unwrap();

// Verify: forward then inverse equals identity
// S then S† = I; H then H = I (Hadamard is self-inverse)
```

---

## Quantum-Classical Hybrid Operations

### Pattern-to-QASM Pipeline

Integration with `transduction_2tdx.rs`:

```
TopologicalPattern
    ↓
PatternExpr (algebraic structure)
    ↓
RewriteRule (pattern matching)
    ↓
HybridCircuit (quantum circuit)
    ↓
OpenQASM 3.0 Code
```

### Example: CRDT E-Graph to Quantum

```rust
let mut egraph = CRDTEGraph::new();

// Add nodes with colors
let red_node = ENode::new("unitary".to_string(), vec![], Color::Red);
let blue_node = ENode::new("inverse".to_string(), vec![], Color::Blue);
let green_node = ENode::new("verify".to_string(), vec![], Color::Green);

egraph.add_node(red_node)?;
egraph.add_node(blue_node)?;
egraph.add_node(green_node)?;

// Generate quantum circuit from e-graph structure
let circuit = transducer.generate_from_egraph(&egraph, "crdt_quantum".to_string())?;

// 3 qubits (one per node), gates assigned by color:
// q0: h q[0];     (RED → Hadamard)
// q1: sdg q[1];   (BLUE → S-dagger)
// q2: id q[2];    (GREEN → Identity)
// Then measurements
```

---

## Circuit Metrics

### Depth Calculation

```rust
let stats = transducer.circuit_stats("circuit_name")?;

// Returns CircuitStats:
// - depth: Critical path length (1 = single layer, 2 = sequential gates)
// - gate_count: Total number of operations
// - qubit_count: Number of qubits used
// - two_qubit_gates: Number of entangling operations
```

### Example Circuit Analysis

```
Circuit: superposition
├─ Depth: 2
├─ Gates: 3 (H, CX, Measure)
├─ Qubits: 2
└─ Two-qubit gates: 1 (CX)
```

---

## Supported Gates

### Single-Qubit

| Gate | Function | QASM |
|------|----------|------|
| X    | Pauli-X (NOT) | `x q[0];` |
| Y    | Pauli-Y | `y q[0];` |
| Z    | Pauli-Z | `z q[0];` |
| H    | Hadamard | `h q[0];` |
| S    | Phase gate | `s q[0];` |
| T    | π/8 gate | `t q[0];` |
| Sdg  | S-dagger | `sdg q[0];` |
| Tdg  | T-dagger | `tdg q[0];` |
| RX   | Rotation X-axis | `rx(π/4) q[0];` |
| RY   | Rotation Y-axis | `ry(π/4) q[0];` |
| RZ   | Rotation Z-axis | `rz(π/4) q[0];` |
| Id   | Identity | `id q[0];` |

### Two-Qubit

| Gate | Function | QASM |
|------|----------|------|
| CX   | CNOT | `cx q[0], q[1];` |
| CY   | Controlled-Y | `cy q[0], q[1];` |
| CZ   | Controlled-Z | `cz q[0], q[1];` |
| SWAP | Swap qubits | `swap q[0], q[1];` |

### Measurement

| Operation | QASM |
|-----------|------|
| Measure   | `measure q[0] -> c[0];` |

---

## Integration with Fermyon Deployment

### HTTP API Extensions

Add these endpoints to agent handlers:

```rust
// Generate QASM circuit from pattern
POST /agent/:id/qasm/from-pattern
Body: { pattern_name: "superposition", num_qubits: 3 }
Response: { circuit_name: "...", qasm_code: "...", depth: 2 }

// Export QASM code
GET /agent/:id/qasm/:circuit_name
Response: { qasm: "OPENQASM 3.0;..." }

// Circuit statistics
GET /agent/:id/qasm/:circuit_name/stats
Response: { depth: 2, gate_count: 5, two_qubit_gates: 1 }
```

### NATS Message Integration

Circuit generation messages:

```
qasm.generate.pattern      → Request QASM from pattern
qasm.optimize.circuit      → Optimize and return
qasm.export.qasm          → Export OPENQASM code
qasm.stats.request        → Get circuit metrics
```

---

## Test Coverage (15 Tests)

| Test | Purpose |
|------|---------|
| `test_quantum_gate_from_color` | Color→gate mapping |
| `test_gate_qasm` | QASM code generation |
| `test_gate_inverse` | Gate inversion |
| `test_circuit_creation` | Circuit initialization |
| `test_circuit_depth` | Depth calculation |
| `test_transducer` | Transducer registration |
| `test_qasm_export` | QASM export |
| `test_inverse_circuit` | Circuit reversal |
| `test_circuit_optimization` | Identity gate removal |
| `test_circuit_validation` | Qubit index checking |
| `test_circuit_stats` | Metrics calculation |
| `test_parameterized_circuit` | Variational ansatz |
| `test_egraph_to_circuit` | E-graph→quantum |
| `test_gate_scheduling` | Operation ordering |
| `test_hybrid_control_flow` | Classical control |

---

## Performance Characteristics

### Circuit Compilation

- **Gate to QASM**: O(1) per gate
- **Circuit depth**: O(n) where n = number of gates
- **Optimization**: O(n) for identity removal
- **Validation**: O(m) where m = number of qubits

### Memory Usage

- Circuit storage: ~100 bytes per gate (instruction + metadata)
- QASM string: ~50 bytes per instruction
- Parameters: ~8 bytes per parameter

---

## Limitations & Future Work

### Current (Phase 3C+)

✅ Single-qubit and two-qubit gates
✅ Parameterized circuits (VQE/QAOA support)
✅ Measurement and classical collapse
✅ Circuit optimization (identity removal)
✅ Reversibility (adjoint generation)

### Future Enhancements

🔲 Multi-qubit controlled gates (MCX, MCY, MCZ)
🔲 Custom gate definitions
🔲 Error mitigation (zero-noise extrapolation)
🔲 Quantum state tomography
🔲 Circuit equivalence checking
🔲 Hardware-specific compilation (device-aware)
🔲 Hybrid variational algorithms (VQE integration)
🔲 Distributed quantum simulation

---

## Example: Full Workflow

```rust
use fermyon_agents::*;

fn main() -> Result<(), String> {
    // Create transducer
    let mut transducer = QasmTransducer::new();

    // Create parameterized VQE ansatz (3 qubits, 2 layers)
    let circuit = transducer.generate_parameterized_circuit(
        "vqe_ansatz".to_string(),
        3,
        2,
    );

    // Check depth and gate count
    let stats = transducer.circuit_stats("vqe_ansatz")?;
    println!("Circuit depth: {}", stats.depth);
    println!("Gate count: {}", stats.gate_count);

    // Generate inverse (for state tomography)
    let inv = transducer.inverse_circuit("vqe_ansatz")?;

    // Export both as QASM
    let forward_qasm = transducer.export_qasm("vqe_ansatz")?;
    let inverse_qasm = transducer.export_qasm(&inv)?;

    println!("Forward:\n{}", forward_qasm);
    println!("Inverse:\n{}", inverse_qasm);

    Ok(())
}
```

---

## References

- **OpenQASM 3.0**: https://openqasm.com/
- **3-Coloring CRDT**: E-graph constraint satisfaction
- **Variational Quantum**: VQE and QAOA algorithms
- **Quantum Gates**: Standard quantum computing references

---

**Status**: ✅ Implemented in Phase 3C+
**Lines of Code**: 300 (qasm_integration.rs)
**Test Coverage**: 15 tests
**Integration**: P1+ component, exported from lib.rs
