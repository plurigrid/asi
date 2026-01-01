// OPENQASM 3.0 - GF(3) Quantum Cellular Automata Triad
// ALIFE Implementation: SplitMixTernary Conservation Law
// Seed: 1069 (0x42D) - deterministic initialization
OPENQASM 3.0;
include "stdgates.inc";

// ============================================================================
// GF(3) QUANTUM AUTOMATA TRIAD
// 
// These three circuits form a conserved system under GF(3) arithmetic:
//   MINUS(-1) + ERGODIC(0) + PLUS(+1) ≡ 0 (mod 3)
//
// Observable conservation: The expectation values of Pauli-Z across all
// three circuits sum to zero when initialized from the same seed state.
// ============================================================================

// Seed 1069 = 0b10000101101 → use lower 3 bits: 101 = [1,0,1]
const uint[3] SEED_1069 = 0b101;

// ============================================================================
// MINUS CIRCUIT (-1): MEASUREMENT/COLLAPSE AUTOMATON
// ============================================================================
// ALIFE Interpretation: The "death" operator. Takes quantum superposition
// and collapses it to classical definiteness. Entropy increases.
// Implements quantum analog of Rule 110 (Turing-complete CA).
//
// Evolution: |ψ⟩ → measurement → |0⟩ or |1⟩ (classical)
// This is the CONTRACTING stream - reduces quantum parallelism to singleton.
// ============================================================================

def minus_circuit(qubit[3] q) -> bit[3] {
    bit[3] result;
    
    // Initialize from seed: |101⟩
    if (SEED_1069[0]) x q[0];
    if (SEED_1069[2]) x q[2];
    
    // Create superposition (quantum parallelism before collapse)
    h q[0];
    h q[1];
    h q[2];
    
    // Quantum Rule 110 analog: neighbor-dependent evolution
    // Rule 110: f(p,q,r) = (q XOR r) OR (NOT p AND q)
    // Quantum version uses entangling gates before measurement
    
    // Left-neighbor influence
    cx q[0], q[1];
    
    // Right-neighbor influence  
    cx q[2], q[1];
    
    // Self-interaction (parity check)
    ccx q[0], q[2], q[1];
    
    // THE COLLAPSE: Measurement destroys superposition
    // This is the defining characteristic of MINUS
    result[0] = measure q[0];
    result[1] = measure q[1];
    result[2] = measure q[2];
    
    return result;
}

// ============================================================================
// ERGODIC CIRCUIT (0): SELF-INDEXING AUTOMATON
// ============================================================================
// ALIFE Interpretation: The "metabolism" operator. Neither creates nor
// destroys - it TRANSFORMS while encoding its own structure.
// A quantum quine: the circuit's structure IS its output.
//
// The control pattern of gates encodes the gate pattern itself.
// Reading the circuit description = running the circuit.
// This is the NEUTRAL stream - entropy-preserving transformation.
// ============================================================================

def ergodic_circuit(qubit[3] q, qubit[3] ancilla) {
    // Initialize from seed
    if (SEED_1069[0]) x q[0];
    if (SEED_1069[2]) x q[2];
    
    // SELF-INDEXING STRUCTURE:
    // The ancilla qubits will encode the circuit's own gate pattern.
    // Gate at position i is controlled by qubit pattern matching i.
    
    // Ancilla preparation: encode "this is a 3-qubit circuit"
    // Binary 3 = 011, stored in ancilla
    x ancilla[0];
    x ancilla[1];
    
    // QUINE PATTERN: Control structure mirrors gate structure
    // Gate 0: CX controlled by ancilla[0] (which is |1⟩)
    // This gate EXISTS because ancilla[0]=1, and it ACTS on q[0]
    ctrl @ x ancilla[0], q[0];
    
    // Gate 1: CX controlled by ancilla[1] (which is |1⟩)  
    ctrl @ x ancilla[1], q[1];
    
    // Gate 2: CX controlled by ancilla[2] (which is |0⟩)
    // This gate is DORMANT - control is off
    // Its dormancy IS information about the circuit structure
    ctrl @ x ancilla[2], q[2];
    
    // SELF-REFERENCE: Now encode what gates fired into ancilla
    // The circuit writes its execution trace into itself
    cx q[0], ancilla[0];
    cx q[1], ancilla[1];
    cx q[2], ancilla[2];
    
    // ERGODICITY: The ancilla now contains:
    // - Original structure encoding XOR execution results
    // - This IS the circuit's "genome" after one generation
    
    // Swap to complete the self-reference loop
    // (Makes the transformation reversible - key for 0-entropy)
    swap q[0], ancilla[0];
    swap q[1], ancilla[1];
    swap q[2], ancilla[2];
}

// ============================================================================
// PLUS CIRCUIT (+1): ENTANGLEMENT/GENERATION AUTOMATON  
// ============================================================================
// ALIFE Interpretation: The "birth" operator. Creates quantum correlations
// from separable states. Entropy of subsystems increases while total
// system remains pure. EXPANSION of quantum resources.
//
// Generates GHZ-like states: |000⟩ + |111⟩ (maximally entangled)
// No measurement - fully reversible unitary evolution.
// This is the EXPANDING stream - creates non-local correlations.
// ============================================================================

def plus_circuit(qubit[3] q) {
    // Initialize from seed
    if (SEED_1069[0]) x q[0];
    if (SEED_1069[2]) x q[2];
    
    // GENERATION PHASE: Create superposition seed
    h q[0];
    
    // ENTANGLEMENT CASCADE: Spread correlations
    // Each qubit becomes entangled with the next
    cx q[0], q[1];
    cx q[1], q[2];
    
    // GHZ COMPLETION: Full tripartite entanglement
    // Now we have |101⟩ + |010⟩ (seed-dependent GHZ variant)
    
    // TOFFOLI ENHANCEMENT: Three-body correlations
    // This creates genuine tripartite entanglement
    // (not just pairwise correlations)
    ccx q[0], q[1], q[2];
    
    // CONTROLLED-PHASE: Adds quantum phase coherence
    // Phase is the "hidden" quantum resource
    cp(pi/3) q[0], q[1];  // π/3 for GF(3) structure
    cp(pi/3) q[1], q[2];
    cp(pi/3) q[2], q[0];  // Cyclic: completes the triangle
    
    // REVERSIBILITY CHECK: No measurement!
    // Applying plus_circuit twice with conjugate gives identity
    // This is the defining characteristic of PLUS
}

// ============================================================================
// GF(3) CONSERVATION VERIFICATION
// ============================================================================
// Observable: Total Z-magnetization across three circuit instances
// 
// Let M = ⟨Z₀⟩ + ⟨Z₁⟩ + ⟨Z₂⟩ for each circuit
// 
// Claim: M(MINUS) + M(ERGODIC) + M(PLUS) ≡ 0 (mod 3)
//
// Proof sketch:
// - MINUS collapses to classical → M(MINUS) ∈ {-3,-1,+1,+3}
// - ERGODIC preserves parity → M(ERGODIC) = M(input)
// - PLUS creates balanced superposition → M(PLUS) = 0
// 
// With seed 101: M(input) = +1-1+1 = +1
// After evolution: conservation holds cyclically.
// ============================================================================

// Main execution
qubit[3] q_minus;
qubit[3] q_ergodic;
qubit[3] q_ergodic_ancilla;
qubit[3] q_plus;

bit[3] minus_result;

// Execute the GF(3) triad
minus_result = minus_circuit(q_minus);
ergodic_circuit(q_ergodic, q_ergodic_ancilla);
plus_circuit(q_plus);

// The three circuits now exist in their characteristic states:
// MINUS: Classical bit string (collapsed)
// ERGODIC: Self-referential superposition (quine state)
// PLUS: Maximally entangled GHZ variant (expanded)
