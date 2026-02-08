package main

// ═══════════════════════════════════════════════════════════════════════════════
// BISIMULATION ADVERSARIAL GAME
// ═══════════════════════════════════════════════════════════════════════════════
//
// Two-player game for security technique analysis:
//   - Attacker: Tries to distinguish security states (exploit differences)
//   - Defender: Maintains equivalence (shows mitigations work equally)
//   - Arbiter: Verifies GF(3) conservation
//
// THREE WORLDS (from gayzip.gay):
//   🔴 ZAHN#   seed=1069  ORDER MATTERS     ⊗ tensor        Ungar Games
//   🟢 JULES#  seed=69    ORDER AGNOSTIC    ⊕ coproduct     Bisimulation
//   🔵 FABRIZ# seed=0     ORDER ENTANGLED   ⊛ convolution   Both/Neither
//
// The JOIN-SEMILATTICE enables Ungar Games by providing:
//   1. Partial order on attack/defense states
//   2. Least upper bounds (joins) for combining observations
//   3. Prerequisite chains as lattice paths (order matters!)
//
// ═══════════════════════════════════════════════════════════════════════════════

import (
	"fmt"
	"sort"
)

// ═══════════════════════════════════════════════════════════════════════════════
// SEEDS - The Three Worlds
// ═══════════════════════════════════════════════════════════════════════════════

const (
	SEED_ZAHN   uint64 = 1069 // 🔴 ORDER MATTERS (Ungar Games)
	SEED_JULES  uint64 = 69   // 🟢 ORDER AGNOSTIC (Bisimulation)
	SEED_FABRIZ uint64 = 0    // 🔵 ORDER ENTANGLED (Both/Neither)
)

// Trit represents GF(3) values: -1, 0, +1
type Trit int8

const (
	TritNeg  Trit = -1 // Attacker
	TritZero Trit = 0  // Arbiter
	TritPos  Trit = +1 // Defender
)

// ═══════════════════════════════════════════════════════════════════════════════
// JOIN-SEMILATTICE FOR SECURITY STATES
// ═══════════════════════════════════════════════════════════════════════════════

// SecurityState represents a point in the attack/defense lattice
type SecurityState struct {
	TechniquesExecuted []string // Techniques that have been executed
	DefensesActive     []string // Active defenses
	RiskLevel          int      // Cumulative risk (0-10)
	Compromised        bool     // Has the system been compromised?
}

// JoinSemilattice provides partial order with least upper bounds
type JoinSemilattice struct {
	States    map[string]*SecurityState
	Ordering  map[string][]string // state -> states it dominates (less than)
	Bottom    *SecurityState      // Least element (no attacks, full defense)
	Top       *SecurityState      // Greatest element (full compromise)
}

// NewJoinSemilattice creates a security state lattice
func NewJoinSemilattice() *JoinSemilattice {
	return &JoinSemilattice{
		States:   make(map[string]*SecurityState),
		Ordering: make(map[string][]string),
		Bottom: &SecurityState{
			TechniquesExecuted: []string{},
			DefensesActive:     []string{"all"},
			RiskLevel:          0,
			Compromised:        false,
		},
		Top: &SecurityState{
			TechniquesExecuted: []string{"full-compromise"},
			DefensesActive:     []string{},
			RiskLevel:          10,
			Compromised:        true,
		},
	}
}

// Join computes the least upper bound of two security states
func (l *JoinSemilattice) Join(s1, s2 *SecurityState) *SecurityState {
	// Merge techniques (union)
	techSet := make(map[string]bool)
	for _, t := range s1.TechniquesExecuted {
		techSet[t] = true
	}
	for _, t := range s2.TechniquesExecuted {
		techSet[t] = true
	}
	techniques := make([]string, 0, len(techSet))
	for t := range techSet {
		techniques = append(techniques, t)
	}
	sort.Strings(techniques)

	// Intersect defenses (only defenses surviving both)
	defSet := make(map[string]bool)
	for _, d := range s1.DefensesActive {
		defSet[d] = true
	}
	defenses := []string{}
	for _, d := range s2.DefensesActive {
		if defSet[d] {
			defenses = append(defenses, d)
		}
	}

	// Risk is maximum
	risk := s1.RiskLevel
	if s2.RiskLevel > risk {
		risk = s2.RiskLevel
	}

	return &SecurityState{
		TechniquesExecuted: techniques,
		DefensesActive:     defenses,
		RiskLevel:          risk,
		Compromised:        s1.Compromised || s2.Compromised,
	}
}

// LessThan checks if s1 ≤ s2 in the lattice (s1 is less compromised)
func (l *JoinSemilattice) LessThan(s1, s2 *SecurityState) bool {
	// s1 ≤ s2 iff:
	// - s1.Techniques ⊆ s2.Techniques (fewer attacks)
	// - s1.Defenses ⊇ s2.Defenses (more defenses)
	// - s1.Risk ≤ s2.Risk

	// Check techniques subset
	s2Techs := make(map[string]bool)
	for _, t := range s2.TechniquesExecuted {
		s2Techs[t] = true
	}
	for _, t := range s1.TechniquesExecuted {
		if !s2Techs[t] {
			return false
		}
	}

	// Check defenses superset
	s1Defs := make(map[string]bool)
	for _, d := range s1.DefensesActive {
		s1Defs[d] = true
	}
	for _, d := range s2.DefensesActive {
		if !s1Defs[d] {
			return false
		}
	}

	return s1.RiskLevel <= s2.RiskLevel
}

// ═══════════════════════════════════════════════════════════════════════════════
// UNGAR GAME - ORDER MATTERS (Tensor ⊗)
// ═══════════════════════════════════════════════════════════════════════════════
//
// In Ungar Games, the ORDER of technique execution matters:
//   - reconnaissance → initial-access → execution → persistence
//   - You CANNOT do lateral-movement before initial-access
//   - The tensor product ⊗ is non-commutative: a⊗b ≠ b⊗a
//
// This is enforced via the Prerequisites field in Technique.

// UngarGame represents an order-dependent attack game
type UngarGame struct {
	KB              *BlackHatGoKnowledge
	Lattice         *JoinSemilattice
	AttackChain     []*Technique // Ordered sequence (order matters!)
	CurrentState    *SecurityState
	Seed            uint64
	History         []GameMove
	GF3Balance      Trit // Must sum to 0 (mod 3)
}

// GameMove represents a single move in the game
type GameMove struct {
	Round     int
	Role      string // "attacker", "defender", "arbiter"
	Action    string
	Technique string
	Defense   string
	Trit      Trit
	StateHash string
}

// NewUngarGame creates an order-dependent attack game
func NewUngarGame(kb *BlackHatGoKnowledge) *UngarGame {
	return &UngarGame{
		KB:      kb,
		Lattice: NewJoinSemilattice(),
		AttackChain: []*Technique{},
		CurrentState: &SecurityState{
			TechniquesExecuted: []string{},
			DefensesActive:     getAllDefenseIDs(kb),
			RiskLevel:          0,
			Compromised:        false,
		},
		Seed:       SEED_ZAHN, // Ungar uses ZAHN seed
		History:    []GameMove{},
		GF3Balance: 0,
	}
}

// CanExecute checks if a technique can be executed given current state
// ORDER MATTERS: Prerequisites must be satisfied
func (g *UngarGame) CanExecute(techID string) (bool, string) {
	tech, exists := g.KB.Techniques[techID]
	if !exists {
		return false, fmt.Sprintf("technique %s not found", techID)
	}

	// Check prerequisites (ORDER CONSTRAINT from Ungar)
	executed := make(map[string]bool)
	for _, t := range g.CurrentState.TechniquesExecuted {
		executed[t] = true
	}

	for _, prereq := range tech.Prerequisites {
		if !executed[prereq] {
			return false, fmt.Sprintf("prerequisite %s not satisfied (order matters!)", prereq)
		}
	}

	return true, ""
}

// AttackerMove attempts to execute a technique (Attacker turn)
func (g *UngarGame) AttackerMove(techID string) (bool, *SecurityState, error) {
	canExec, reason := g.CanExecute(techID)
	if !canExec {
		return false, g.CurrentState, fmt.Errorf("cannot execute: %s", reason)
	}

	tech := g.KB.Techniques[techID]

	// Execute technique
	newTechs := append([]string{}, g.CurrentState.TechniquesExecuted...)
	newTechs = append(newTechs, techID)

	// Remove bypassed defenses
	mitigations := g.KB.GetMitigations(techID)
	defSet := make(map[string]bool)
	for _, d := range g.CurrentState.DefensesActive {
		defSet[d] = true
	}
	for _, m := range mitigations {
		// If defense exists but is bypassed by this technique
		if defSet[m.ID] && tech.RiskLevel >= 8 {
			delete(defSet, m.ID)
		}
	}
	newDefs := make([]string, 0, len(defSet))
	for d := range defSet {
		newDefs = append(newDefs, d)
	}

	newState := &SecurityState{
		TechniquesExecuted: newTechs,
		DefensesActive:     newDefs,
		RiskLevel:          g.CurrentState.RiskLevel + tech.RiskLevel/2,
		Compromised:        tech.RiskLevel >= 9,
	}

	// Record move with Attacker trit (-1)
	g.History = append(g.History, GameMove{
		Round:     len(g.History) + 1,
		Role:      "attacker",
		Action:    "execute",
		Technique: techID,
		Trit:      TritNeg,
		StateHash: hashState(newState),
	})
	g.GF3Balance = (g.GF3Balance + TritNeg) % 3

	g.CurrentState = newState
	g.AttackChain = append(g.AttackChain, tech)

	return true, newState, nil
}

// DefenderMove attempts to deploy a defense (Defender turn)
func (g *UngarGame) DefenderMove(defenseID string) (bool, *SecurityState, error) {
	def, exists := g.KB.Defenses[defenseID]
	if !exists {
		return false, g.CurrentState, fmt.Errorf("defense %s not found", defenseID)
	}

	// Add defense if not already active
	newDefs := append([]string{}, g.CurrentState.DefensesActive...)
	found := false
	for _, d := range newDefs {
		if d == defenseID {
			found = true
			break
		}
	}
	if !found {
		newDefs = append(newDefs, defenseID)
	}

	// Reduce risk based on defense effectiveness
	riskReduction := int(def.Effectiveness * 2)
	newRisk := g.CurrentState.RiskLevel - riskReduction
	if newRisk < 0 {
		newRisk = 0
	}

	newState := &SecurityState{
		TechniquesExecuted: g.CurrentState.TechniquesExecuted,
		DefensesActive:     newDefs,
		RiskLevel:          newRisk,
		Compromised:        g.CurrentState.Compromised && def.Effectiveness < 0.9,
	}

	// Record move with Defender trit (+1)
	g.History = append(g.History, GameMove{
		Round:   len(g.History) + 1,
		Role:    "defender",
		Action:  "deploy",
		Defense: defenseID,
		Trit:    TritPos,
		StateHash: hashState(newState),
	})
	g.GF3Balance = (g.GF3Balance + TritPos) % 3

	g.CurrentState = newState

	return true, newState, nil
}

// ArbiterVerify checks GF(3) conservation (Arbiter turn)
func (g *UngarGame) ArbiterVerify() (bool, Trit) {
	// Sum all trits
	var total Trit = 0
	for _, move := range g.History {
		total = (total + move.Trit) % 3
	}

	conserved := total == 0 || len(g.History)%3 != 0

	// Record arbiter move with trit that balances
	balancingTrit := Trit((-int(total) % 3 + 3) % 3)
	if balancingTrit == 2 {
		balancingTrit = -1
	}

	g.History = append(g.History, GameMove{
		Round:  len(g.History) + 1,
		Role:   "arbiter",
		Action: "verify",
		Trit:   balancingTrit,
	})
	g.GF3Balance = (g.GF3Balance + balancingTrit) % 3

	return conserved || g.GF3Balance == 0, g.GF3Balance
}

// ═══════════════════════════════════════════════════════════════════════════════
// BISIMULATION GAME - ORDER AGNOSTIC (Coproduct ⊕)
// ═══════════════════════════════════════════════════════════════════════════════
//
// In Bisimulation Games, two security configurations are "equivalent" if
// the Attacker cannot distinguish them. Order doesn't matter for equivalence.
//
// Two states S1, S2 are BISIMILAR if:
//   - For every Attacker move in S1, Defender can match in S2
//   - For every Attacker move in S2, Defender can match in S1
//   - The coproduct ⊕ is commutative: a⊕b = b⊕a

// BisimulationGame represents an order-agnostic equivalence game
type BisimulationGame struct {
	KB       *BlackHatGoKnowledge
	State1   *SecurityState
	State2   *SecurityState
	Lattice  *JoinSemilattice
	Seed     uint64
	History  []GameMove
	MaxDepth int
}

// NewBisimulationGame creates an equivalence checking game
func NewBisimulationGame(kb *BlackHatGoKnowledge, s1, s2 *SecurityState) *BisimulationGame {
	return &BisimulationGame{
		KB:       kb,
		State1:   s1,
		State2:   s2,
		Lattice:  NewJoinSemilattice(),
		Seed:     SEED_JULES, // Bisimulation uses JULES seed
		History:  []GameMove{},
		MaxDepth: 10,
	}
}

// AreBisimilar checks if two security states are behaviorally equivalent
func (g *BisimulationGame) AreBisimilar() bool {
	return g.checkBisimilar(g.State1, g.State2, 0)
}

func (g *BisimulationGame) checkBisimilar(s1, s2 *SecurityState, depth int) bool {
	if depth >= g.MaxDepth {
		return true // Assume bisimilar if we can't distinguish after max depth
	}

	// For each technique Attacker could try in s1
	for techID, tech := range g.KB.Techniques {
		// Can Attacker execute in s1?
		s1Techs := make(map[string]bool)
		for _, t := range s1.TechniquesExecuted {
			s1Techs[t] = true
		}

		canInS1 := true
		for _, prereq := range tech.Prerequisites {
			if !s1Techs[prereq] {
				canInS1 = false
				break
			}
		}

		if canInS1 {
			// Defender must be able to match in s2
			s2Techs := make(map[string]bool)
			for _, t := range s2.TechniquesExecuted {
				s2Techs[t] = true
			}

			canInS2 := true
			for _, prereq := range tech.Prerequisites {
				if !s2Techs[prereq] {
					canInS2 = false
					break
				}
			}

			if canInS1 && !canInS2 {
				// Attacker wins: found a distinguishing move!
				g.History = append(g.History, GameMove{
					Round:     len(g.History) + 1,
					Role:      "attacker",
					Action:    "distinguish",
					Technique: techID,
					Trit:      TritNeg,
				})
				return false
			}
		}
	}

	// Check symmetric direction (s2 → s1)
	for techID, tech := range g.KB.Techniques {
		s2Techs := make(map[string]bool)
		for _, t := range s2.TechniquesExecuted {
			s2Techs[t] = true
		}

		canInS2 := true
		for _, prereq := range tech.Prerequisites {
			if !s2Techs[prereq] {
				canInS2 = false
				break
			}
		}

		if canInS2 {
			s1Techs := make(map[string]bool)
			for _, t := range s1.TechniquesExecuted {
				s1Techs[t] = true
			}

			canInS1 := true
			for _, prereq := range tech.Prerequisites {
				if !s1Techs[prereq] {
					canInS1 = false
					break
				}
			}

			if canInS2 && !canInS1 {
				g.History = append(g.History, GameMove{
					Round:     len(g.History) + 1,
					Role:      "attacker",
					Action:    "distinguish",
					Technique: techID,
					Trit:      TritNeg,
				})
				return false
			}
		}
	}

	// Defender matched all moves
	g.History = append(g.History, GameMove{
		Round:  len(g.History) + 1,
		Role:   "defender",
		Action: "match_all",
		Trit:   TritPos,
	})

	return true
}

// ═══════════════════════════════════════════════════════════════════════════════
// FABRIZ GAME - ORDER ENTANGLED (Convolution ⊛)
// ═══════════════════════════════════════════════════════════════════════════════
//
// Fabriz world combines both: (a⊗b) ⊕ (b⊗a)
// This is the SUPERPOSITION of both orderings.
// Used when we want to analyze BOTH ordered attack chains AND their equivalence.

// FabrizGame represents an entangled order game
type FabrizGame struct {
	Ungar       *UngarGame
	Bisim       *BisimulationGame
	Seed        uint64
	Entanglement float64 // 0.0 = pure Ungar, 1.0 = pure Bisim
}

// NewFabrizGame creates an entangled game from both perspectives
func NewFabrizGame(kb *BlackHatGoKnowledge) *FabrizGame {
	ungar := NewUngarGame(kb)
	bisim := NewBisimulationGame(kb, ungar.CurrentState, ungar.CurrentState)

	return &FabrizGame{
		Ungar:        ungar,
		Bisim:        bisim,
		Seed:         SEED_FABRIZ,
		Entanglement: 0.5, // Equal weight to both
	}
}

// Convolve computes ⊛: the superposition of both orders
func (g *FabrizGame) Convolve(techID1, techID2 string) (*SecurityState, *SecurityState, bool) {
	// Create two Ungar games
	game1 := NewUngarGame(g.Ungar.KB)
	game2 := NewUngarGame(g.Ungar.KB)

	// Execute in both orders
	game1.AttackerMove(techID1)
	game1.AttackerMove(techID2)

	game2.AttackerMove(techID2)
	game2.AttackerMove(techID1)

	// Check if they're bisimilar
	bisim := NewBisimulationGame(g.Ungar.KB, game1.CurrentState, game2.CurrentState)
	equivalent := bisim.AreBisimilar()

	return game1.CurrentState, game2.CurrentState, equivalent
}

// ═══════════════════════════════════════════════════════════════════════════════
// ATTACK CHAIN ANALYSIS
// ═══════════════════════════════════════════════════════════════════════════════

// AttackChain represents an ordered sequence of techniques
type AttackChain struct {
	Techniques   []*Technique
	TotalRisk    int
	Prerequisites map[string][]string
	IsValid      bool
	Errors       []string
}

// ValidateChain checks if an attack chain is valid (Ungar-compliant)
func ValidateChain(kb *BlackHatGoKnowledge, techIDs []string) *AttackChain {
	chain := &AttackChain{
		Techniques:    make([]*Technique, 0),
		Prerequisites: make(map[string][]string),
		IsValid:       true,
		Errors:        []string{},
	}

	executed := make(map[string]bool)

	for _, id := range techIDs {
		tech, exists := kb.Techniques[id]
		if !exists {
			chain.IsValid = false
			chain.Errors = append(chain.Errors, fmt.Sprintf("technique %s not found", id))
			continue
		}

		// Check prerequisites (ORDER MATTERS!)
		for _, prereq := range tech.Prerequisites {
			if !executed[prereq] {
				chain.IsValid = false
				chain.Errors = append(chain.Errors,
					fmt.Sprintf("technique %s requires %s first (Ungar constraint)", id, prereq))
			}
		}

		chain.Techniques = append(chain.Techniques, tech)
		chain.TotalRisk += tech.RiskLevel
		chain.Prerequisites[id] = tech.Prerequisites
		executed[id] = true
	}

	return chain
}

// GetValidChains returns all valid attack chains up to given length
func GetValidChains(kb *BlackHatGoKnowledge, maxLen int) [][]string {
	var results [][]string

	// Get all techniques with no prerequisites (entry points)
	entryPoints := []string{}
	for id, tech := range kb.Techniques {
		if len(tech.Prerequisites) == 0 {
			entryPoints = append(entryPoints, id)
		}
	}

	// BFS to find valid chains
	type state struct {
		chain    []string
		executed map[string]bool
	}

	queue := []state{}
	for _, ep := range entryPoints {
		queue = append(queue, state{
			chain:    []string{ep},
			executed: map[string]bool{ep: true},
		})
	}

	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]

		if len(current.chain) <= maxLen {
			results = append(results, current.chain)
		}

		if len(current.chain) >= maxLen {
			continue
		}

		// Find next valid techniques
		for id, tech := range kb.Techniques {
			if current.executed[id] {
				continue
			}

			// Check all prerequisites satisfied
			valid := true
			for _, prereq := range tech.Prerequisites {
				if !current.executed[prereq] {
					valid = false
					break
				}
			}

			if valid {
				newChain := append([]string{}, current.chain...)
				newChain = append(newChain, id)
				newExecuted := make(map[string]bool)
				for k, v := range current.executed {
					newExecuted[k] = v
				}
				newExecuted[id] = true
				queue = append(queue, state{chain: newChain, executed: newExecuted})
			}
		}
	}

	return results
}

// ═══════════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════════

func getAllDefenseIDs(kb *BlackHatGoKnowledge) []string {
	ids := make([]string, 0, len(kb.Defenses))
	for id := range kb.Defenses {
		ids = append(ids, id)
	}
	sort.Strings(ids)
	return ids
}

func hashState(s *SecurityState) string {
	return fmt.Sprintf("T%d-D%d-R%d-C%v",
		len(s.TechniquesExecuted),
		len(s.DefensesActive),
		s.RiskLevel,
		s.Compromised)
}

// SplitMix64 deterministic RNG (matching Gay.jl)
func SplitMix64(state uint64) (uint64, uint64) {
	state += 0x9e3779b97f4a7c15
	z := state
	z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9
	z = (z ^ (z >> 27)) * 0x94d049bb133111eb
	return z ^ (z >> 31), state
}

// ColorFromSeed generates deterministic RGB from seed
func ColorFromSeed(seed uint64) (r, g, b uint8) {
	h1, s := SplitMix64(seed)
	h2, s := SplitMix64(s)
	h3, _ := SplitMix64(s)

	return uint8(h1 >> 56), uint8(h2 >> 56), uint8(h3 >> 56)
}

// TritFromSeed extracts GF(3) trit from seed
func TritFromSeed(seed uint64) Trit {
	h, _ := SplitMix64(seed)
	return Trit((h % 3) - 1) // -1, 0, or +1
}

// ═══════════════════════════════════════════════════════════════════════════════
// PRINTABLE GAME TRANSCRIPT
// ═══════════════════════════════════════════════════════════════════════════════

func (g *UngarGame) PrintTranscript() {
	fmt.Println("╔══════════════════════════════════════════════════════════════════════╗")
	fmt.Println("║                 UNGAR GAME TRANSCRIPT (ORDER MATTERS)                ║")
	fmt.Println("╠══════════════════════════════════════════════════════════════════════╣")
	fmt.Printf("║ Seed: %d (ZAHN world)                                                ║\n", g.Seed)
	fmt.Printf("║ Attack Chain Length: %d                                              ║\n", len(g.AttackChain))
	fmt.Println("╠══════════════════════════════════════════════════════════════════════╣")

	for _, move := range g.History {
		role := "?"
		switch move.Role {
		case "attacker":
			role = "🔴 ATTACKER"
		case "defender":
			role = "🟢 DEFENDER"
		case "arbiter":
			role = "🔵 ARBITER "
		}

		action := move.Action
		if move.Technique != "" {
			action = fmt.Sprintf("%s: %s", action, move.Technique)
		}
		if move.Defense != "" {
			action = fmt.Sprintf("%s: %s", action, move.Defense)
		}

		fmt.Printf("║ Round %d: %s (%+d) - %s\n", move.Round, role, move.Trit, action)
	}

	fmt.Println("╠══════════════════════════════════════════════════════════════════════╣")
	fmt.Printf("║ GF(3) Balance: %+d (conserved: %v)                                   ║\n",
		g.GF3Balance, g.GF3Balance == 0)
	fmt.Printf("║ Final Risk Level: %d/10                                              ║\n",
		g.CurrentState.RiskLevel)
	fmt.Printf("║ Compromised: %v                                                      ║\n",
		g.CurrentState.Compromised)
	fmt.Println("╚══════════════════════════════════════════════════════════════════════╝")
}
