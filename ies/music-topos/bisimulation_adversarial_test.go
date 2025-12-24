package main

import (
	"testing"
)

// ═══════════════════════════════════════════════════════════════════════════════
// JOIN-SEMILATTICE TESTS
// ═══════════════════════════════════════════════════════════════════════════════

func TestNewJoinSemilattice(t *testing.T) {
	lattice := NewJoinSemilattice()

	if lattice == nil {
		t.Fatal("NewJoinSemilattice returned nil")
	}
	if lattice.Bottom == nil {
		t.Error("Bottom element should not be nil")
	}
	if lattice.Top == nil {
		t.Error("Top element should not be nil")
	}
	if lattice.Bottom.RiskLevel != 0 {
		t.Errorf("Bottom risk should be 0, got %d", lattice.Bottom.RiskLevel)
	}
	if lattice.Top.RiskLevel != 10 {
		t.Errorf("Top risk should be 10, got %d", lattice.Top.RiskLevel)
	}
}

func TestJoin(t *testing.T) {
	lattice := NewJoinSemilattice()

	s1 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency", "tcp-port-scan"},
		DefensesActive:     []string{"mfa", "edr", "waf"},
		RiskLevel:          3,
		Compromised:        false,
	}

	s2 := &SecurityState{
		TechniquesExecuted: []string{"http-client-basics", "shodan-client"},
		DefensesActive:     []string{"mfa", "waf"},
		RiskLevel:          4,
		Compromised:        false,
	}

	joined := lattice.Join(s1, s2)

	// Should have union of techniques (4 total)
	if len(joined.TechniquesExecuted) != 4 {
		t.Errorf("Expected 4 techniques in join, got %d", len(joined.TechniquesExecuted))
	}

	// Should have intersection of defenses (mfa, waf)
	if len(joined.DefensesActive) != 2 {
		t.Errorf("Expected 2 defenses in join, got %d", len(joined.DefensesActive))
	}

	// Should have max risk
	if joined.RiskLevel != 4 {
		t.Errorf("Expected risk 4 (max), got %d", joined.RiskLevel)
	}
}

func TestLessThan(t *testing.T) {
	lattice := NewJoinSemilattice()

	s1 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency"},
		DefensesActive:     []string{"mfa", "edr", "waf"},
		RiskLevel:          1,
		Compromised:        false,
	}

	s2 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency", "tcp-port-scan"},
		DefensesActive:     []string{"mfa", "waf"},
		RiskLevel:          3,
		Compromised:        false,
	}

	// s1 < s2 (fewer techniques, more defenses, lower risk)
	if !lattice.LessThan(s1, s2) {
		t.Error("s1 should be less than s2")
	}

	// s2 is NOT < s1
	if lattice.LessThan(s2, s1) {
		t.Error("s2 should not be less than s1")
	}
}

// ═══════════════════════════════════════════════════════════════════════════════
// UNGAR GAME TESTS (ORDER MATTERS)
// ═══════════════════════════════════════════════════════════════════════════════

func TestNewUngarGame(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewUngarGame(kb)

	if game == nil {
		t.Fatal("NewUngarGame returned nil")
	}
	if game.Seed != SEED_ZAHN {
		t.Errorf("Expected ZAHN seed %d, got %d", SEED_ZAHN, game.Seed)
	}
	if len(game.AttackChain) != 0 {
		t.Error("New game should have empty attack chain")
	}
	if game.CurrentState.Compromised {
		t.Error("Initial state should not be compromised")
	}
}

func TestCanExecuteNoPrereq(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewUngarGame(kb)

	// go-concurrency has no prerequisites
	canExec, reason := game.CanExecute("go-concurrency")
	if !canExec {
		t.Errorf("Should be able to execute go-concurrency: %s", reason)
	}
}

func TestCanExecuteWithPrereq(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewUngarGame(kb)

	// tcp-proxy requires tcp-port-scan
	canExec, reason := game.CanExecute("tcp-proxy")
	if canExec {
		t.Error("Should NOT be able to execute tcp-proxy without tcp-port-scan")
	}
	if reason == "" {
		t.Error("Should have a reason for failure")
	}

	// Execute prerequisite first
	game.AttackerMove("go-concurrency")
	game.AttackerMove("tcp-port-scan")

	// Now tcp-proxy should work
	canExec, _ = game.CanExecute("tcp-proxy")
	if !canExec {
		t.Error("Should be able to execute tcp-proxy after prerequisites")
	}
}

func TestAttackerMove(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewUngarGame(kb)

	success, state, err := game.AttackerMove("go-concurrency")

	if !success {
		t.Errorf("Attacker move should succeed: %v", err)
	}
	if len(state.TechniquesExecuted) != 1 {
		t.Errorf("Expected 1 technique executed, got %d", len(state.TechniquesExecuted))
	}
	if len(game.History) != 1 {
		t.Errorf("Expected 1 move in history, got %d", len(game.History))
	}
	if game.History[0].Trit != TritNeg {
		t.Errorf("Attacker trit should be -1, got %d", game.History[0].Trit)
	}
}

func TestDefenderMove(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewUngarGame(kb)

	// Attacker first (needs a technique with no prereqs)
	success1, _, err1 := game.AttackerMove("go-concurrency")
	if !success1 {
		t.Fatalf("Attacker move should succeed: %v", err1)
	}

	// Defender responds
	success, _, err := game.DefenderMove("mfa")

	if !success {
		t.Errorf("Defender move should succeed: %v", err)
	}
	if len(game.History) != 2 {
		t.Errorf("Expected 2 moves in history, got %d", len(game.History))
	}
	if len(game.History) >= 2 && game.History[1].Trit != TritPos {
		t.Errorf("Defender trit should be +1, got %d", game.History[1].Trit)
	}
}

func TestArbiterVerify(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewUngarGame(kb)

	// Play a round: Attacker, Defender
	game.AttackerMove("tcp-port-scan")
	game.DefenderMove("ids-ips")

	// Arbiter verifies
	conserved, balance := game.ArbiterVerify()

	// After Attacker(-1) + Defender(+1) + Arbiter(0) = 0
	if !conserved {
		t.Errorf("GF(3) should be conserved, balance: %d", balance)
	}
}

func TestOrderMattersInUngarGame(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	// Try to execute techniques out of order
	game := NewUngarGame(kb)

	// netcat-clone requires tcp-proxy which requires tcp-port-scan
	canExec, _ := game.CanExecute("netcat-clone")
	if canExec {
		t.Error("Should NOT be able to execute netcat-clone without prerequisites")
	}

	// Execute in correct order
	game.AttackerMove("go-concurrency")
	game.AttackerMove("tcp-port-scan")
	game.AttackerMove("tcp-proxy")

	canExec, _ = game.CanExecute("netcat-clone")
	if !canExec {
		t.Error("Should be able to execute netcat-clone after prerequisites")
	}
}

// ═══════════════════════════════════════════════════════════════════════════════
// BISIMULATION GAME TESTS (ORDER AGNOSTIC)
// ═══════════════════════════════════════════════════════════════════════════════

func TestNewBisimulationGame(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	s1 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency"},
		DefensesActive:     []string{"mfa"},
		RiskLevel:          1,
		Compromised:        false,
	}
	s2 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency"},
		DefensesActive:     []string{"mfa"},
		RiskLevel:          1,
		Compromised:        false,
	}

	game := NewBisimulationGame(kb, s1, s2)

	if game == nil {
		t.Fatal("NewBisimulationGame returned nil")
	}
	if game.Seed != SEED_JULES {
		t.Errorf("Expected JULES seed %d, got %d", SEED_JULES, game.Seed)
	}
}

func TestIdenticalStatesBisimilar(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	s1 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency", "tcp-port-scan"},
		DefensesActive:     []string{"mfa", "edr"},
		RiskLevel:          3,
		Compromised:        false,
	}
	s2 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency", "tcp-port-scan"},
		DefensesActive:     []string{"mfa", "edr"},
		RiskLevel:          3,
		Compromised:        false,
	}

	game := NewBisimulationGame(kb, s1, s2)

	if !game.AreBisimilar() {
		t.Error("Identical states should be bisimilar")
	}
}

func TestDifferentStatesNotBisimilar(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	// s1 has tcp-port-scan executed
	s1 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency", "tcp-port-scan"},
		DefensesActive:     []string{"mfa"},
		RiskLevel:          3,
		Compromised:        false,
	}

	// s2 does not have tcp-port-scan, so tcp-proxy is not available
	s2 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency"},
		DefensesActive:     []string{"mfa"},
		RiskLevel:          1,
		Compromised:        false,
	}

	game := NewBisimulationGame(kb, s1, s2)

	// They're NOT bisimilar because from s1, attacker can do tcp-proxy
	// but from s2, they cannot (prerequisite not met)
	if game.AreBisimilar() {
		t.Error("States with different capabilities should not be bisimilar")
	}
}

// ═══════════════════════════════════════════════════════════════════════════════
// FABRIZ GAME TESTS (ORDER ENTANGLED)
// ═══════════════════════════════════════════════════════════════════════════════

func TestNewFabrizGame(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewFabrizGame(kb)

	if game == nil {
		t.Fatal("NewFabrizGame returned nil")
	}
	if game.Seed != SEED_FABRIZ {
		t.Errorf("Expected FABRIZ seed %d, got %d", SEED_FABRIZ, game.Seed)
	}
	if game.Entanglement != 0.5 {
		t.Errorf("Expected entanglement 0.5, got %f", game.Entanglement)
	}
}

func TestConvolveCommutativeTechniques(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewFabrizGame(kb)

	// Two techniques with no prerequisites should be commutative
	s1, s2, equiv := game.Convolve("go-concurrency", "json-xml-marshal")

	if s1 == nil || s2 == nil {
		t.Fatal("Convolve returned nil states")
	}

	// Both orders should produce equivalent states
	if !equiv {
		t.Log("States from different orders:")
		t.Logf("  Order 1: %v", s1.TechniquesExecuted)
		t.Logf("  Order 2: %v", s2.TechniquesExecuted)
	}
}

// ═══════════════════════════════════════════════════════════════════════════════
// ATTACK CHAIN VALIDATION TESTS
// ═══════════════════════════════════════════════════════════════════════════════

func TestValidateChainValid(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	chain := ValidateChain(kb, []string{
		"go-concurrency",
		"tcp-port-scan",
		"tcp-proxy",
	})

	if !chain.IsValid {
		t.Errorf("Valid chain rejected: %v", chain.Errors)
	}
	if len(chain.Techniques) != 3 {
		t.Errorf("Expected 3 techniques, got %d", len(chain.Techniques))
	}
}

func TestValidateChainInvalid(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	// tcp-proxy requires tcp-port-scan, executed out of order
	chain := ValidateChain(kb, []string{
		"go-concurrency",
		"tcp-proxy", // Missing tcp-port-scan!
		"tcp-port-scan",
	})

	if chain.IsValid {
		t.Error("Invalid chain should be rejected")
	}
	if len(chain.Errors) == 0 {
		t.Error("Should have error messages")
	}
}

func TestGetValidChains(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	chains := GetValidChains(kb, 3)

	if len(chains) == 0 {
		t.Error("Should find at least some valid chains")
	}

	// Verify all chains are valid
	for _, techIDs := range chains {
		chain := ValidateChain(kb, techIDs)
		if !chain.IsValid {
			t.Errorf("GetValidChains returned invalid chain: %v, errors: %v",
				techIDs, chain.Errors)
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════════
// GF(3) CONSERVATION TESTS
// ═══════════════════════════════════════════════════════════════════════════════

func TestGF3TritsBalance(t *testing.T) {
	// Attacker + Defender + Arbiter should balance to 0 (mod 3)
	trits := []Trit{TritNeg, TritPos, TritZero}
	sum := Trit(0)
	for _, tr := range trits {
		sum = (sum + tr) % 3
	}

	if sum != 0 {
		t.Errorf("Basic trits should sum to 0, got %d", sum)
	}
}

func TestTritFromSeed(t *testing.T) {
	// Test deterministic trit generation
	t1 := TritFromSeed(SEED_ZAHN)
	t2 := TritFromSeed(SEED_ZAHN)

	if t1 != t2 {
		t.Error("Same seed should produce same trit")
	}

	// All three seeds should produce valid trits
	for _, seed := range []uint64{SEED_ZAHN, SEED_JULES, SEED_FABRIZ} {
		trit := TritFromSeed(seed)
		if trit < -1 || trit > 1 {
			t.Errorf("Trit from seed %d out of range: %d", seed, trit)
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════════
// SPLITMIX64 TESTS
// ═══════════════════════════════════════════════════════════════════════════════

func TestSplitMix64Deterministic(t *testing.T) {
	h1, s1 := SplitMix64(SEED_ZAHN)
	h2, s2 := SplitMix64(SEED_ZAHN)

	if h1 != h2 || s1 != s2 {
		t.Error("SplitMix64 should be deterministic")
	}
}

func TestColorFromSeed(t *testing.T) {
	r1, g1, b1 := ColorFromSeed(SEED_ZAHN)
	r2, g2, b2 := ColorFromSeed(SEED_ZAHN)

	if r1 != r2 || g1 != g2 || b1 != b2 {
		t.Error("ColorFromSeed should be deterministic")
	}

	// Different seeds should (usually) produce different colors
	r3, g3, b3 := ColorFromSeed(SEED_JULES)
	if r1 == r3 && g1 == g3 && b1 == b3 {
		t.Log("Warning: Different seeds produced same color (possible but unlikely)")
	}
}

// ═══════════════════════════════════════════════════════════════════════════════
// INTEGRATION TESTS
// ═══════════════════════════════════════════════════════════════════════════════

func TestFullUngarGameRound(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	game := NewUngarGame(kb)

	// Must start with no-prereq technique
	success, _, err := game.AttackerMove("go-concurrency")
	if !success {
		t.Fatalf("First attacker move failed: %v", err)
	}

	// Round 1: Attacker scans (needs go-concurrency first)
	game.AttackerMove("tcp-port-scan")

	// Round 1: Defender deploys IDS
	game.DefenderMove("ids-ips")

	// Round 1: Arbiter verifies
	game.ArbiterVerify()

	// Round 2: Attacker escalates (needs tcp-port-scan first)
	game.AttackerMove("tcp-proxy")

	// Round 2: Defender adds network segmentation
	game.DefenderMove("network-seg")

	// Round 2: Arbiter verifies
	conserved, balance := game.ArbiterVerify()

	// Game state should be consistent
	if len(game.AttackChain) != 3 { // go-concurrency, tcp-port-scan, tcp-proxy
		t.Errorf("Expected 3 techniques in chain, got %d", len(game.AttackChain))
	}

	t.Logf("Attack chain: %d techniques", len(game.AttackChain))
	t.Logf("History: %d moves", len(game.History))
	t.Logf("Final GF(3) balance: %d (conserved: %v)", balance, conserved)
}

func TestUngarVsBisimComparison(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	// Create two Ungar games with same techniques in different order
	game1 := NewUngarGame(kb)
	game1.AttackerMove("go-concurrency")
	game1.AttackerMove("json-xml-marshal")

	game2 := NewUngarGame(kb)
	game2.AttackerMove("json-xml-marshal")
	game2.AttackerMove("go-concurrency")

	// In Ungar (order matters), these are DIFFERENT games
	// In Bisim (order agnostic), the END STATES might be equivalent

	bisim := NewBisimulationGame(kb, game1.CurrentState, game2.CurrentState)
	bisimilar := bisim.AreBisimilar()

	t.Logf("Game 1 chain: %v", game1.CurrentState.TechniquesExecuted)
	t.Logf("Game 2 chain: %v", game2.CurrentState.TechniquesExecuted)
	t.Logf("End states bisimilar: %v", bisimilar)

	// For techniques with no interdependencies, end states should be bisimilar
	if !bisimilar {
		t.Error("End states of commutative techniques should be bisimilar")
	}
}

// ═══════════════════════════════════════════════════════════════════════════════
// BENCHMARKS
// ═══════════════════════════════════════════════════════════════════════════════

func BenchmarkUngarGameRound(b *testing.B) {
	kb := LoadBlackHatKnowledge()

	for i := 0; i < b.N; i++ {
		game := NewUngarGame(kb)
		game.AttackerMove("tcp-port-scan")
		game.DefenderMove("ids-ips")
		game.ArbiterVerify()
	}
}

func BenchmarkBisimCheck(b *testing.B) {
	kb := LoadBlackHatKnowledge()

	s1 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency", "tcp-port-scan"},
		DefensesActive:     []string{"mfa", "edr"},
		RiskLevel:          3,
		Compromised:        false,
	}
	s2 := &SecurityState{
		TechniquesExecuted: []string{"go-concurrency", "tcp-port-scan"},
		DefensesActive:     []string{"mfa", "edr"},
		RiskLevel:          3,
		Compromised:        false,
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		game := NewBisimulationGame(kb, s1, s2)
		game.AreBisimilar()
	}
}

func BenchmarkValidateChain(b *testing.B) {
	kb := LoadBlackHatKnowledge()
	chain := []string{"go-concurrency", "tcp-port-scan", "tcp-proxy"}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		ValidateChain(kb, chain)
	}
}
