// WiringDiagram.cue - Compositional skill wiring with validation
//
// CUE is a constraint-based configuration language that validates
// wiring diagrams against type and balance constraints.
//
// This implements Spivak's wiring diagram semantics for skills.

package wiringdiagram

// GF(3) trit values
#Trit: -1 | 0 | 1

// A Port is a typed connection point
#Port: {
	name: string & =~"^[a-z][a-zA-Z0-9_]*$"
	type: string
	direction: "in" | "out"
}

// A Skill node in the wiring diagram
#Skill: {
	name: string & =~"^[a-z][a-z0-9-]*$"
	trit: #Trit
	inputs: [...#Port] | *[]
	outputs: [...#Port] | *[]
	category: string | *"uncategorized"
	
	// Modelica-style connectors (effort/flow pairs)
	connectors: [...#Connector] | *[]
}

// Modelica-style connector with effort/flow semantics
#Connector: {
	name: string
	effort: string    // Across variable (voltage, pressure, etc.)
	flow: string      // Through variable (current, flow rate, etc.)
	trit: #Trit | *0  // Default to ergodic for connectors
}

// A Wire connects two ports
#Wire: {
	from: {
		skill: string
		port: string
	}
	to: {
		skill: string
		port: string
	}
}

// A Wiring Diagram is a collection of skills and wires
#WiringDiagram: {
	name: string
	description: string | *""
	
	// The skills (boxes) in the diagram
	skills: [Name=string]: #Skill & {name: Name}
	
	// The wires (connections) between skills
	wires: [...#Wire]
	
	// Outer interface: the exposed ports of the composite
	interface: {
		inputs: [...#Port] | *[]
		outputs: [...#Port] | *[]
	}
	
	// === CONSTRAINT: Wire types must match ===
	_checkWires: [for w in wires {
		_fromSkill: skills[w.from.skill]
		_toSkill:   skills[w.to.skill]
		
		// Find matching ports
		_fromPort: [for p in _fromSkill.outputs if p.name == w.from.port {p}][0]
		_toPort:   [for p in _toSkill.inputs if p.name == w.to.port {p}][0]
		
		// Types must match
		_typeMatch: _fromPort.type == _toPort.type
		_typeMatch: true  // Enforce the constraint
	}]
	
	// === CONSTRAINT: GF(3) conservation ===
	// Sum of all skill trits must be ≡ 0 (mod 3)
	_tritValues: [for s in skills {s.trit}]
	_tritSum: list.Sum(_tritValues)
	_balanced: mod(_tritSum, 3) == 0
	
	// Allow unbalanced diagrams but mark them
	balanced: _balanced
}

// A Triad is a wiring diagram with exactly 3 skills
#Triad: #WiringDiagram & {
	_skillCount: len(skills)
	_skillCount: 3
	balanced: true  // Triads must be balanced
}

// === EXAMPLE: UNWORLD Federation Triad ===
unworldFederation: #Triad & {
	name: "unworld-federation"
	description: "The three UNWORLD agents form a balanced triad"
	
	skills: {
		causality: {
			trit: 1
			category: "federation"
			outputs: [{name: "generation", type: "SkillGraph", direction: "out"}]
		}
		"two-monad": {
			trit: 0
			category: "federation"
			inputs: [{name: "skills", type: "SkillGraph", direction: "in"}]
			outputs: [{name: "coordinated", type: "SkillGraph", direction: "out"}]
		}
		amp: {
			trit: -1
			category: "federation"
			inputs: [{name: "proposal", type: "SkillGraph", direction: "in"}]
			outputs: [{name: "verified", type: "SkillGraph", direction: "out"}]
		}
	}
	
	wires: [
		{from: {skill: "causality", port: "generation"}, to: {skill: "two-monad", port: "skills"}},
		{from: {skill: "two-monad", port: "coordinated"}, to: {skill: "amp", port: "proposal"}}
	]
	
	interface: {
		outputs: [{name: "verified", type: "SkillGraph", direction: "out"}]
	}
}

// === EXAMPLE: Mathematical Verification Triad ===
mathVerification: #Triad & {
	name: "math-verification"
	description: "Polynomial operads + temporal coalgebra + sheaf cohomology"
	
	skills: {
		"poly-operads": {
			trit: 1
			category: "mathematics"
			outputs: [{name: "composition", type: "WiringDiagram", direction: "out"}]
		}
		"temporal-coalgebra": {
			trit: 0
			category: "mathematics"
			inputs: [{name: "diagram", type: "WiringDiagram", direction: "in"}]
			outputs: [{name: "dynamics", type: "Coalgebra", direction: "out"}]
		}
		"sheaf-cohomology": {
			trit: -1
			category: "mathematics"
			inputs: [{name: "structure", type: "Coalgebra", direction: "in"}]
			outputs: [{name: "verified", type: "Bool", direction: "out"}]
		}
	}
	
	wires: [
		{from: {skill: "poly-operads", port: "composition"}, to: {skill: "temporal-coalgebra", port: "diagram"}},
		{from: {skill: "temporal-coalgebra", port: "dynamics"}, to: {skill: "sheaf-cohomology", port: "structure"}}
	]
	
	interface: {
		outputs: [{name: "verified", type: "Bool", direction: "out"}]
	}
}

// === EXAMPLE: Modelica Simulation Triad ===
modelicaSimulation: #Triad & {
	name: "modelica-simulation"
	description: "Acausal modeling with stochastic and probabilistic verification"
	
	skills: {
		"langevin-dynamics": {
			trit: 1
			category: "physics"
			outputs: [{name: "trajectory", type: "Trajectory", direction: "out"}]
			connectors: [{name: "thermal", effort: "Temperature", flow: "HeatFlow", trit: 0}]
		}
		modelica: {
			trit: 0
			category: "simulation"
			inputs: [{name: "model", type: "Equations", direction: "in"}]
			outputs: [{name: "solution", type: "Trajectory", direction: "out"}]
			connectors: [
				{name: "electrical", effort: "Voltage", flow: "Current"},
				{name: "mechanical", effort: "Force", flow: "Velocity"}
			]
		}
		"fokker-planck": {
			trit: -1
			category: "physics"
			inputs: [{name: "ensemble", type: "Trajectory", direction: "in"}]
			outputs: [{name: "distribution", type: "Probability", direction: "out"}]
		}
	}
	
	wires: [
		{from: {skill: "langevin-dynamics", port: "trajectory"}, to: {skill: "modelica", port: "model"}},
		{from: {skill: "modelica", port: "solution"}, to: {skill: "fokker-planck", port: "ensemble"}}
	]
	
	interface: {
		outputs: [{name: "distribution", type: "Probability", direction: "out"}]
	}
}

// === Composition: Triads can be composed into larger diagrams ===
#ComposedDiagram: {
	triads: [...#Triad]
	
	// Connection points between triads
	interTriadWires: [...{
		fromTriad: string
		fromPort: string
		toTriad: string
		toPort: string
	}]
	
	// The composed diagram is balanced iff all triads are balanced
	balanced: and([for t in triads {t.balanced}])
}

// === Validation helpers ===

// Check that a skill has at least one connection
#ConnectedSkill: #Skill & {
	_hasConnections: len(inputs) + len(outputs) + len(connectors) > 0
	_hasConnections: true
}

// Check that a diagram has no orphan skills
#NoOrphans: #WiringDiagram & {
	_allConnected: [for name, skill in skills {
		_inWires: [for w in wires if w.to.skill == name || w.from.skill == name {w}]
		_connected: len(_inWires) > 0 || len(skill.inputs) == 0 && len(skill.outputs) == 0
		_connected: true
	}]
}
