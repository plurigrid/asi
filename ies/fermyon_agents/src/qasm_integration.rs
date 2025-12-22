/*!
   qasm-integration: 3-Colorable Quantum Circuits

   P1+ Component: Maps CRDT 3-coloring to OpenQASM quantum gates
   - RED: Forward unitary operations
   - BLUE: Inverse/adjoint operations
   - GREEN: Measurement/identity (verification)
*/

use crate::Color;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum QuantumGate {
    X, Y, Z, H, S, T, Sdg, Tdg,
    RX(f64), RY(f64), RZ(f64),
    CX, CY, CZ, SWAP,
    Measure, Id,
}

impl QuantumGate {
    pub fn from_color(color: Color) -> Self {
        match color {
            Color::Red => QuantumGate::H,      // Forward superposition
            Color::Blue => QuantumGate::Sdg,   // Inverse operation
            Color::Green => QuantumGate::Id,   // Identity/measurement
        }
    }

    pub fn to_qasm(&self, targets: &[usize]) -> String {
        match self {
            QuantumGate::X => format!("x q[{}];", targets[0]),
            QuantumGate::Y => format!("y q[{}];", targets[0]),
            QuantumGate::Z => format!("z q[{}];", targets[0]),
            QuantumGate::H => format!("h q[{}];", targets[0]),
            QuantumGate::S => format!("s q[{}];", targets[0]),
            QuantumGate::T => format!("t q[{}];", targets[0]),
            QuantumGate::Sdg => format!("sdg q[{}];", targets[0]),
            QuantumGate::Tdg => format!("tdg q[{}];", targets[0]),
            QuantumGate::RX(a) => format!("rx({}) q[{}];", a, targets[0]),
            QuantumGate::RY(a) => format!("ry({}) q[{}];", a, targets[0]),
            QuantumGate::RZ(a) => format!("rz({}) q[{}];", a, targets[0]),
            QuantumGate::CX => format!("cx q[{}], q[{}];", targets[0], targets[1]),
            QuantumGate::CY => format!("cy q[{}], q[{}];", targets[0], targets[1]),
            QuantumGate::CZ => format!("cz q[{}], q[{}];", targets[0], targets[1]),
            QuantumGate::SWAP => format!("swap q[{}], q[{}];", targets[0], targets[1]),
            QuantumGate::Measure => format!("measure q[{}] -> c[{}];", targets[0], targets[0]),
            QuantumGate::Id => format!("id q[{}];", targets[0]),
        }
    }

    pub fn inverse(&self) -> Self {
        match self {
            QuantumGate::S => QuantumGate::Sdg,
            QuantumGate::Sdg => QuantumGate::S,
            QuantumGate::T => QuantumGate::Tdg,
            QuantumGate::Tdg => QuantumGate::T,
            QuantumGate::RX(a) => QuantumGate::RX(-a),
            QuantumGate::RY(a) => QuantumGate::RY(-a),
            QuantumGate::RZ(a) => QuantumGate::RZ(-a),
            other => other.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct CircuitInstruction {
    pub gate: QuantumGate,
    pub targets: Vec<usize>,
}

impl CircuitInstruction {
    pub fn new(gate: QuantumGate, targets: Vec<usize>) -> Self {
        Self { gate, targets }
    }

    pub fn to_qasm(&self) -> String {
        self.gate.to_qasm(&self.targets)
    }
}

#[derive(Debug, Clone)]
pub struct HybridCircuit {
    pub name: String,
    pub num_qubits: usize,
    pub num_bits: usize,
    pub instructions: Vec<CircuitInstruction>,
    pub parameters: HashMap<String, f64>,
}

impl HybridCircuit {
    pub fn new(name: String, num_qubits: usize, num_bits: usize) -> Self {
        Self {
            name,
            num_qubits,
            num_bits,
            instructions: vec![],
            parameters: HashMap::new(),
        }
    }

    pub fn add_gate(&mut self, gate: QuantumGate, targets: Vec<usize>) {
        self.instructions.push(CircuitInstruction::new(gate, targets));
    }

    pub fn to_qasm_code(&self) -> String {
        let mut qasm = format!(
            "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[{}] q;\nbit[{}] c;\n\n// {}\n",
            self.num_qubits, self.num_bits, self.name
        );
        for instr in &self.instructions {
            qasm.push_str(&format!("{}\n", instr.to_qasm()));
        }
        qasm
    }

    pub fn depth(&self) -> usize {
        if self.instructions.is_empty() { return 0; }
        let mut qubit_depth = vec![0; self.num_qubits];
        let mut max = 0;
        for instr in &self.instructions {
            let current_max = instr.targets.iter().map(|&q| qubit_depth[q]).max().unwrap_or(0);
            for &q in &instr.targets {
                qubit_depth[q] = current_max + 1;
            }
            max = max.max(current_max + 1);
        }
        max
    }

    pub fn gate_count(&self) -> usize {
        self.instructions.len()
    }
}

pub struct QasmTransducer {
    pub circuits: HashMap<String, HybridCircuit>,
    pub color_gate_map: HashMap<Color, QuantumGate>,
}

impl QasmTransducer {
    pub fn new() -> Self {
        let mut color_gate_map = HashMap::new();
        color_gate_map.insert(Color::Red, QuantumGate::H);
        color_gate_map.insert(Color::Blue, QuantumGate::Sdg);
        color_gate_map.insert(Color::Green, QuantumGate::Id);
        Self {
            circuits: HashMap::new(),
            color_gate_map,
        }
    }

    pub fn register_circuit(&mut self, circuit: HybridCircuit) {
        self.circuits.insert(circuit.name.clone(), circuit);
    }

    pub fn optimize_circuit(&mut self, name: &str) -> Result<(), String> {
        let circuit = self.circuits.get_mut(name)
            .ok_or_else(|| format!("Circuit not found: {}", name))?;
        circuit.instructions.retain(|i| i.gate != QuantumGate::Id);
        Ok(())
    }

    pub fn validate_circuit(&self, name: &str) -> Result<(), String> {
        let circuit = self.circuits.get(name)
            .ok_or_else(|| format!("Circuit not found: {}", name))?;
        for instr in &circuit.instructions {
            for &q in &instr.targets {
                if q >= circuit.num_qubits {
                    return Err(format!("Invalid qubit: {}", q));
                }
            }
        }
        Ok(())
    }

    pub fn inverse_circuit(&mut self, name: &str) -> Result<String, String> {
        let circuit = self.circuits.get(name)
            .ok_or_else(|| format!("Circuit not found: {}", name))?
            .clone();
        let inv_name = format!("{}_inverse", name);
        let mut inv = HybridCircuit::new(inv_name.clone(), circuit.num_qubits, circuit.num_bits);
        for instr in circuit.instructions.iter().rev() {
            inv.add_gate(instr.gate.inverse(), instr.targets.clone());
        }
        self.circuits.insert(inv.name.clone(), inv);
        Ok(inv_name)
    }

    pub fn export_qasm(&self, name: &str) -> Result<String, String> {
        self.circuits.get(name)
            .map(|c| c.to_qasm_code())
            .ok_or_else(|| format!("Circuit not found: {}", name))
    }
}

impl Default for QasmTransducer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quantum_gate_from_color() {
        assert_eq!(QuantumGate::from_color(Color::Red), QuantumGate::H);
        assert_eq!(QuantumGate::from_color(Color::Blue), QuantumGate::Sdg);
        assert_eq!(QuantumGate::from_color(Color::Green), QuantumGate::Id);
    }

    #[test]
    fn test_gate_qasm() {
        assert_eq!(QuantumGate::X.to_qasm(&[0]), "x q[0];");
        assert_eq!(QuantumGate::CX.to_qasm(&[0, 1]), "cx q[0], q[1];");
    }

    #[test]
    fn test_gate_inverse() {
        assert_eq!(QuantumGate::S.inverse(), QuantumGate::Sdg);
        assert_eq!(QuantumGate::Sdg.inverse(), QuantumGate::S);
    }

    #[test]
    fn test_circuit_creation() {
        let c = HybridCircuit::new("test".to_string(), 2, 2);
        assert_eq!(c.num_qubits, 2);
        assert_eq!(c.gate_count(), 0);
    }

    #[test]
    fn test_circuit_depth() {
        let mut c = HybridCircuit::new("test".to_string(), 2, 2);
        c.add_gate(QuantumGate::H, vec![0]);
        assert_eq!(c.depth(), 1);
        c.add_gate(QuantumGate::CX, vec![0, 1]);
        assert_eq!(c.depth(), 2);
    }

    #[test]
    fn test_transducer() {
        let mut t = QasmTransducer::new();
        let c = HybridCircuit::new("test".to_string(), 2, 2);
        t.register_circuit(c);
        assert_eq!(t.circuits.len(), 1);
    }

    #[test]
    fn test_qasm_export() {
        let mut c = HybridCircuit::new("test".to_string(), 2, 2);
        c.add_gate(QuantumGate::H, vec![0]);
        let qasm = c.to_qasm_code();
        assert!(qasm.contains("OPENQASM"));
        assert!(qasm.contains("h q[0];"));
    }

    #[test]
    fn test_inverse_circuit() {
        let mut t = QasmTransducer::new();
        let mut c = HybridCircuit::new("test".to_string(), 2, 2);
        c.add_gate(QuantumGate::S, vec![0]);
        t.register_circuit(c);
        let inv = t.inverse_circuit("test").unwrap();
        assert!(t.circuits.contains_key(&inv));
    }
}
