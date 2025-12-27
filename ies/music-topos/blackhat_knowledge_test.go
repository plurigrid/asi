package main

import (
	"testing"
)

func TestLoadBlackHatKnowledge(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	if kb == nil {
		t.Fatal("LoadBlackHatKnowledge returned nil")
	}

	// Test technique count (expanded: book + macOS + Cloud/Mobile/IoT + SupplyChain/API/Web3/AI/RedTeam + ATT&CK/OWASP LLM)
	if len(kb.Techniques) < 186 {
		t.Errorf("Expected at least 186 techniques, got %d", len(kb.Techniques))
	}

	// Test tool count (30 previous + 6 new = 36)
	if len(kb.Tools) < 36 {
		t.Errorf("Expected at least 36 tools, got %d", len(kb.Tools))
	}

	// Test defense count (26 previous + 6 new = 32)
	if len(kb.Defenses) < 32 {
		t.Errorf("Expected at least 32 defenses, got %d", len(kb.Defenses))
	}

	// Test exploit count
	if len(kb.Exploits) != 6 {
		t.Errorf("Expected 6 exploits, got %d", len(kb.Exploits))
	}
}

func TestGetTechniquesByChapter(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	tests := []struct {
		chapter  int
		minCount int
	}{
		{1, 2},  // Go Fundamentals
		{2, 3},  // TCP, Scanners, Proxies
		{3, 3},  // HTTP Clients
		{4, 3},  // HTTP Servers
		{5, 3},  // DNS
		{6, 3},  // SMB/NTLM
		{7, 3},  // Databases
		{8, 2},  // Packet Processing
		{9, 4},  // Exploit Code
		{10, 2}, // Plugins
		{11, 5}, // Crypto
		{12, 3}, // Windows
		{13, 2}, // Steganography
		{14, 3}, // RAT
	}

	for _, tt := range tests {
		techniques := kb.GetTechniquesByChapter(tt.chapter)
		if len(techniques) < tt.minCount {
			t.Errorf("Chapter %d: expected at least %d techniques, got %d",
				tt.chapter, tt.minCount, len(techniques))
		}
	}
}

func TestGetTechniquesByCategory(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	categories := []string{"Network", "Web", "Exploitation", "Evasion", "Crypto", "Windows", "Foundation"}

	for _, cat := range categories {
		techniques := kb.GetTechniquesByCategory(cat)
		if len(techniques) == 0 {
			t.Errorf("Category %s has no techniques", cat)
		}
	}
}

func TestGetHighRiskTechniques(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	highRisk := kb.GetHighRiskTechniques(8)
	if len(highRisk) < 10 {
		t.Errorf("Expected at least 10 high-risk techniques (>=8), got %d", len(highRisk))
	}

	// Verify all returned techniques have risk >= 8
	for _, tech := range highRisk {
		if tech.RiskLevel < 8 {
			t.Errorf("Technique %s has risk %d, expected >= 8", tech.ID, tech.RiskLevel)
		}
	}

	// Test critical techniques (risk 10)
	critical := kb.GetHighRiskTechniques(10)
	if len(critical) < 3 {
		t.Errorf("Expected at least 3 critical techniques (risk 10), got %d", len(critical))
	}
}

func TestGetMitigations(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	tests := []struct {
		techniqueID string
		expectMin   int
	}{
		{"credential-harvester", 2}, // WAF + MFA
		{"process-injection", 1},    // EDR
		{"dns-tunneling", 2},        // IDS + DNS monitoring
		{"smb-password-guess", 2},   // Network seg + MFA
	}

	for _, tt := range tests {
		defenses := kb.GetMitigations(tt.techniqueID)
		if len(defenses) < tt.expectMin {
			t.Errorf("Technique %s: expected at least %d mitigations, got %d",
				tt.techniqueID, tt.expectMin, len(defenses))
		}
	}
}

func TestSpecificTechniques(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	// Test key techniques exist with correct properties
	tests := []struct {
		id       string
		chapter  int
		category string
		minRisk  int
	}{
		{"tcp-port-scan", 2, "Network", 3},
		{"credential-harvester", 4, "Web", 7},
		{"pass-the-hash", 6, "Network", 8},
		{"process-injection", 12, "Windows", 9},
		{"grpc-c2", 14, "Evasion", 8},
		{"shellcode-creation", 9, "Exploitation", 9},
	}

	for _, tt := range tests {
		tech, exists := kb.Techniques[tt.id]
		if !exists {
			t.Errorf("Technique %s not found", tt.id)
			continue
		}
		if tech.Chapter != tt.chapter {
			t.Errorf("Technique %s: expected chapter %d, got %d", tt.id, tt.chapter, tech.Chapter)
		}
		if tech.Category != tt.category {
			t.Errorf("Technique %s: expected category %s, got %s", tt.id, tt.category, tech.Category)
		}
		if tech.RiskLevel < tt.minRisk {
			t.Errorf("Technique %s: expected risk >= %d, got %d", tt.id, tt.minRisk, tech.RiskLevel)
		}
	}
}

func TestToolsExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	requiredTools := []string{"gopacket", "miekg-dns", "gorilla-mux", "smb", "grpc"}

	for _, toolID := range requiredTools {
		if _, exists := kb.Tools[toolID]; !exists {
			t.Errorf("Required tool %s not found", toolID)
		}
	}
}

func TestExploitRelationships(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, exploit := range kb.Exploits {
		if exploit.Technique == nil {
			t.Errorf("Exploit %s has nil technique", id)
		}
		if exploit.Target == "" {
			t.Errorf("Exploit %s has empty target", id)
		}
		if exploit.SuccessRate <= 0 || exploit.SuccessRate > 1 {
			t.Errorf("Exploit %s has invalid success rate: %f", id, exploit.SuccessRate)
		}
	}
}

func TestDefenseEffectiveness(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, defense := range kb.Defenses {
		if defense.Effectiveness <= 0 || defense.Effectiveness > 1 {
			t.Errorf("Defense %s has invalid effectiveness: %f", id, defense.Effectiveness)
		}
		if len(defense.Mitigates) == 0 {
			t.Errorf("Defense %s mitigates nothing", id)
		}
	}
}

func BenchmarkLoadBlackHatKnowledge(b *testing.B) {
	for i := 0; i < b.N; i++ {
		LoadBlackHatKnowledge()
	}
}

func BenchmarkGetHighRiskTechniques(b *testing.B) {
	kb := LoadBlackHatKnowledge()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		kb.GetHighRiskTechniques(8)
	}
}

func TestAllChaptersCovered(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for chapter := 1; chapter <= 14; chapter++ {
		techniques := kb.GetTechniquesByChapter(chapter)
		if len(techniques) == 0 {
			t.Errorf("Chapter %d has no techniques", chapter)
		}
	}
}

func TestTechniquePrerequisitesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, tech := range kb.Techniques {
		for _, prereq := range tech.Prerequisites {
			if _, exists := kb.Techniques[prereq]; !exists {
				t.Errorf("Technique %s has non-existent prerequisite: %s", id, prereq)
			}
		}
	}
}

func TestTechniqueIDsMatchKeys(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for key, tech := range kb.Techniques {
		if key != tech.ID {
			t.Errorf("Technique key %s doesn't match ID %s", key, tech.ID)
		}
	}
}

func TestToolIDsMatchKeys(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for key, tool := range kb.Tools {
		if key != tool.ID {
			t.Errorf("Tool key %s doesn't match ID %s", key, tool.ID)
		}
	}
}

func TestDefenseIDsMatchKeys(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for key, defense := range kb.Defenses {
		if key != defense.ID {
			t.Errorf("Defense key %s doesn't match ID %s", key, defense.ID)
		}
	}
}

func TestDefenseMitigatesExistingTechniques(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for defID, defense := range kb.Defenses {
		for _, techID := range defense.Mitigates {
			if _, exists := kb.Techniques[techID]; !exists {
				t.Errorf("Defense %s mitigates non-existent technique: %s", defID, techID)
			}
		}
	}
}

func TestRiskLevelBounds(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, tech := range kb.Techniques {
		if tech.RiskLevel < 0 || tech.RiskLevel > 10 {
			t.Errorf("Technique %s has invalid risk level: %d (must be 0-10)", id, tech.RiskLevel)
		}
	}
}

func TestComplexityValues(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	validComplexities := map[string]bool{"Beginner": true, "Intermediate": true, "Advanced": true}

	for id, tech := range kb.Techniques {
		if !validComplexities[tech.Complexity] {
			t.Errorf("Technique %s has invalid complexity: %s", id, tech.Complexity)
		}
	}
}

func TestCategoryValues(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	validCategories := map[string]bool{
		"Foundation": true, "Network": true, "Web": true,
		"Exploitation": true, "Evasion": true, "Crypto": true, 
		"Windows": true, "macOS": true,
		"Cloud": true, "Mobile": true, "IoT": true,
		"SupplyChain": true, "API": true, "Web3": true, "AI": true, "RedTeam": true,
		"Reconnaissance": true, "ResourceDev": true, "Collection": true, "LateralMovement": true,
	}

	for id, tech := range kb.Techniques {
		if !validCategories[tech.Category] {
			t.Errorf("Technique %s has invalid category: %s", id, tech.Category)
		}
	}
}

func TestToolTypeValues(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	validTypes := map[string]bool{"stdlib": true, "third-party": true, "external": true}

	for id, tool := range kb.Tools {
		if !validTypes[tool.Type] {
			t.Errorf("Tool %s has invalid type: %s", id, tool.Type)
		}
	}
}

func TestImplementationCostValues(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	validCosts := map[string]bool{"Low": true, "Medium": true, "High": true}

	for id, defense := range kb.Defenses {
		if !validCosts[defense.ImplementationCost] {
			t.Errorf("Defense %s has invalid implementation cost: %s", id, defense.ImplementationCost)
		}
	}
}

func TestDetectionRiskValues(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	validRisks := map[string]bool{"Low": true, "Medium": true, "High": true}

	for id, exploit := range kb.Exploits {
		if !validRisks[exploit.DetectionRisk] {
			t.Errorf("Exploit %s has invalid detection risk: %s", id, exploit.DetectionRisk)
		}
	}
}

func TestNoEmptyTechniqueNames(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, tech := range kb.Techniques {
		if tech.Name == "" {
			t.Errorf("Technique %s has empty name", id)
		}
		if tech.Description == "" {
			t.Errorf("Technique %s has empty description", id)
		}
	}
}

func TestNoEmptyToolFields(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, tool := range kb.Tools {
		if tool.Name == "" {
			t.Errorf("Tool %s has empty name", id)
		}
		if tool.Purpose == "" {
			t.Errorf("Tool %s has empty purpose", id)
		}
		if tool.GoImport == "" {
			t.Errorf("Tool %s has empty GoImport", id)
		}
	}
}

func TestNoEmptyDefenseFields(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, defense := range kb.Defenses {
		if defense.Name == "" {
			t.Errorf("Defense %s has empty name", id)
		}
		if defense.Description == "" {
			t.Errorf("Defense %s has empty description", id)
		}
	}
}

func TestToolChapterReferences(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, tool := range kb.Tools {
		if len(tool.UsedInChapters) == 0 {
			t.Errorf("Tool %s has no chapter references", id)
		}
		for _, ch := range tool.UsedInChapters {
			if ch < 1 || ch > 37 { // Extended to chapter 37 for all domains including ATT&CK and LLM
				t.Errorf("Tool %s references invalid chapter: %d", id, ch)
			}
		}
	}
}

func TestExploitTargetNotEmpty(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	for id, exploit := range kb.Exploits {
		if exploit.Target == "" {
			t.Errorf("Exploit %s has empty target", id)
		}
	}
}

func TestNetworkCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	network := kb.GetTechniquesByCategory("Network")
	if len(network) < 8 {
		t.Errorf("Expected at least 8 Network techniques, got %d", len(network))
	}
}

func TestEvasionCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	evasion := kb.GetTechniquesByCategory("Evasion")
	if len(evasion) < 5 {
		t.Errorf("Expected at least 5 Evasion techniques, got %d", len(evasion))
	}
}

func TestCryptoCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	crypto := kb.GetTechniquesByCategory("Crypto")
	if len(crypto) < 5 {
		t.Errorf("Expected at least 5 Crypto techniques, got %d", len(crypto))
	}
}

func TestChapter14RATTechniques(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	ch14 := kb.GetTechniquesByChapter(14)

	hasGRPC := false
	hasImplant := false
	hasServer := false

	for _, tech := range ch14 {
		switch tech.ID {
		case "grpc-c2":
			hasGRPC = true
		case "rat-implant":
			hasImplant = true
		case "rat-server":
			hasServer = true
		}
	}

	if !hasGRPC {
		t.Error("Chapter 14 missing gRPC C2 technique")
	}
	if !hasImplant {
		t.Error("Chapter 14 missing RAT implant technique")
	}
	if !hasServer {
		t.Error("Chapter 14 missing RAT server technique")
	}
}

func TestMFADefenseHighEffectiveness(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	mfa, exists := kb.Defenses["mfa"]
	if !exists {
		t.Fatal("MFA defense not found")
	}
	if mfa.Effectiveness < 0.90 {
		t.Errorf("MFA should have high effectiveness (>90%%), got %.0f%%", mfa.Effectiveness*100)
	}
}

func TestProcessInjectionIsHighRisk(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	pi, exists := kb.Techniques["process-injection"]
	if !exists {
		t.Fatal("Process injection technique not found")
	}
	if pi.RiskLevel < 9 {
		t.Errorf("Process injection should be high risk (>=9), got %d", pi.RiskLevel)
	}
	if pi.Category != "Windows" {
		t.Errorf("Process injection should be Windows category, got %s", pi.Category)
	}
}

func TestGoPackagesNotEmpty(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	// Most techniques should have Go packages (except foundational ones and macOS low-level)
	emptyCount := 0
	for _, tech := range kb.Techniques {
		if len(tech.GoPackages) == 0 && tech.Category != "Foundation" && tech.Category != "macOS" {
			emptyCount++
		}
	}
	// Allow some techniques without packages (advanced techniques often use external tools)
	if emptyCount > 15 {
		t.Errorf("Too many techniques without Go packages: %d", emptyCount)
	}
}

func BenchmarkGetTechniquesByCategory(b *testing.B) {
	kb := LoadBlackHatKnowledge()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		kb.GetTechniquesByCategory("Network")
	}
}

func BenchmarkGetMitigations(b *testing.B) {
	kb := LoadBlackHatKnowledge()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		kb.GetMitigations("process-injection")
	}
}

func BenchmarkGetTechniquesByChapter(b *testing.B) {
	kb := LoadBlackHatKnowledge()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		kb.GetTechniquesByChapter(9)
	}
}

// === macOS-Specific Tests ===

func TestMacOSChaptersCovered(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	macOSChapters := []int{15, 16, 17, 18, 19, 20, 21, 22, 23, 24}
	for _, chapter := range macOSChapters {
		techniques := kb.GetTechniquesByChapter(chapter)
		if len(techniques) < 3 {
			t.Errorf("macOS Chapter %d has fewer than 3 techniques: got %d", chapter, len(techniques))
		}
	}
}

func TestMacOSCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	macos := kb.GetTechniquesByCategory("macOS")
	if len(macos) < 40 {
		t.Errorf("Expected at least 40 macOS techniques, got %d", len(macos))
	}
}

func TestTCCTechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	tccTechniques := []string{"tcc-overview", "tcc-db-read", "tcc-bypass-fda", "tcc-inject"}
	for _, id := range tccTechniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("TCC technique %s not found", id)
		}
	}
}

func TestKeychainTechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	keychainTechniques := []string{"keychain-dump", "keychain-acl", "browser-creds", "icloud-token"}
	for _, id := range keychainTechniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("Keychain technique %s not found", id)
		}
	}
}

func TestPersistenceTechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	persistTechniques := []string{"launchd-persist", "login-items", "cron-persist", "dylib-hijack-persist", "xpc-persist"}
	for _, id := range persistTechniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("Persistence technique %s not found", id)
		}
	}
}

func TestMacOSDefensesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	macosDefenses := []string{"sip-enabled", "tcc-strict", "gatekeeper-strict", "launchd-monitoring", "hardened-runtime"}
	for _, id := range macosDefenses {
		if _, exists := kb.Defenses[id]; !exists {
			t.Errorf("macOS defense %s not found", id)
		}
	}
}

func TestMacOSToolsExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	macosTools := []string{"plist", "zeroconf", "screenshot", "gopsutil", "macho"}
	for _, id := range macosTools {
		if _, exists := kb.Tools[id]; !exists {
			t.Errorf("macOS tool %s not found", id)
		}
	}
}

func TestEDRBypassIsHighRisk(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	edr, exists := kb.Techniques["edr-bypass-macos"]
	if !exists {
		t.Fatal("EDR bypass technique not found")
	}
	if edr.RiskLevel < 8 {
		t.Errorf("EDR bypass should be high risk (>=8), got %d", edr.RiskLevel)
	}
}

func TestUniversalBinaryHasCodeExample(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	ub, exists := kb.Techniques["universal-binary"]
	if !exists {
		t.Fatal("Universal binary technique not found")
	}
	if ub.CodeExample == "" {
		t.Error("Universal binary should have code example")
	}
}

func TestTotalChapterCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	// Should have techniques in chapters 1-37
	for chapter := 1; chapter <= 37; chapter++ {
		techniques := kb.GetTechniquesByChapter(chapter)
		if len(techniques) == 0 {
			t.Errorf("Chapter %d has no techniques", chapter)
		}
	}
}

// === Cloud/Mobile/IoT Tests ===

func TestCloudTechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	cloudTechniques := []string{"k8s-pod-escape", "aws-metadata-ssrf", "docker-socket-abuse", "cloud-cred-harvest"}
	for _, id := range cloudTechniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("Cloud technique %s not found", id)
		}
	}
}

func TestMobileTechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	mobileTechniques := []string{"android-apk-analysis", "android-frida-hooks", "adb-exploitation", "mobile-api-fuzzing"}
	for _, id := range mobileTechniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("Mobile technique %s not found", id)
		}
	}
}

func TestIoTTechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	iotTechniques := []string{"iot-firmware-extract", "mqtt-exploit", "coap-discovery", "uart-serial-hijack", "zigbee-sniff"}
	for _, id := range iotTechniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("IoT technique %s not found", id)
		}
	}
}

func TestNewToolsExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	newTools := []string{"k8s-client-go", "paho-mqtt", "go-coap", "go-serial"}
	for _, id := range newTools {
		if _, exists := kb.Tools[id]; !exists {
			t.Errorf("New tool %s not found", id)
		}
	}
}

func TestNewDefensesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	newDefenses := []string{"imds-v2", "pod-security-policy", "ssl-pinning", "iot-firmware-signing"}
	for _, id := range newDefenses {
		if _, exists := kb.Defenses[id]; !exists {
			t.Errorf("New defense %s not found", id)
		}
	}
}

func TestCloudCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	cloud := kb.GetTechniquesByCategory("Cloud")
	if len(cloud) < 5 {
		t.Errorf("Expected at least 5 Cloud techniques, got %d", len(cloud))
	}
}

func TestMobileCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	mobile := kb.GetTechniquesByCategory("Mobile")
	if len(mobile) < 5 {
		t.Errorf("Expected at least 5 Mobile techniques, got %d", len(mobile))
	}
}

func TestIoTCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	iot := kb.GetTechniquesByCategory("IoT")
	if len(iot) < 5 {
		t.Errorf("Expected at least 5 IoT techniques, got %d", len(iot))
	}
}

// === Supply Chain, API, Web3, AI, RedTeam Tests ===

func TestSupplyChainTechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	techniques := []string{"dependency-confusion", "typosquatting", "cicd-injection", "build-artifact-poison", "lockfile-injection"}
	for _, id := range techniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("SupplyChain technique %s not found", id)
		}
	}
}

func TestAPITechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	techniques := []string{"graphql-introspection", "graphql-batching", "oauth-token-theft", "jwt-none-alg", "api-bola"}
	for _, id := range techniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("API technique %s not found", id)
		}
	}
}

func TestWeb3TechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	techniques := []string{"smart-contract-reentrancy", "flash-loan-exploit", "wallet-drainer", "private-key-extract", "frontrunning-bot"}
	for _, id := range techniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("Web3 technique %s not found", id)
		}
	}
}

func TestAITechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	techniques := []string{"prompt-injection", "model-poisoning", "adversarial-examples", "model-extraction", "llm-jailbreak"}
	for _, id := range techniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("AI technique %s not found", id)
		}
	}
}

func TestRedTeamTechniquesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	techniques := []string{"redirector-setup", "phishing-infra", "c2-rotation", "cloud-terraform-infra", "domain-categorization"}
	for _, id := range techniques {
		if _, exists := kb.Techniques[id]; !exists {
			t.Errorf("RedTeam technique %s not found", id)
		}
	}
}

func TestNewAdvancedToolsExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	tools := []string{"go-ethereum", "golang-jwt", "oauth2", "gonum", "httputil"}
	for _, id := range tools {
		if _, exists := kb.Tools[id]; !exists {
			t.Errorf("Tool %s not found", id)
		}
	}
}

func TestNewAdvancedDefensesExist(t *testing.T) {
	kb := LoadBlackHatKnowledge()

	defenses := []string{"sbom-verification", "cicd-hardening", "graphql-depth-limit", "jwt-validation", 
		"smart-contract-audit", "hardware-wallet", "prompt-guardrails", "model-access-control", "domain-monitoring"}
	for _, id := range defenses {
		if _, exists := kb.Defenses[id]; !exists {
			t.Errorf("Defense %s not found", id)
		}
	}
}

func TestSupplyChainCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	sc := kb.GetTechniquesByCategory("SupplyChain")
	if len(sc) < 5 {
		t.Errorf("Expected at least 5 SupplyChain techniques, got %d", len(sc))
	}
}

func TestAPICategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	api := kb.GetTechniquesByCategory("API")
	if len(api) < 5 {
		t.Errorf("Expected at least 5 API techniques, got %d", len(api))
	}
}

func TestWeb3CategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	web3 := kb.GetTechniquesByCategory("Web3")
	if len(web3) < 5 {
		t.Errorf("Expected at least 5 Web3 techniques, got %d", len(web3))
	}
}

func TestAICategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	ai := kb.GetTechniquesByCategory("AI")
	if len(ai) < 5 {
		t.Errorf("Expected at least 5 AI techniques, got %d", len(ai))
	}
}

func TestRedTeamCategoryCount(t *testing.T) {
	kb := LoadBlackHatKnowledge()
	rt := kb.GetTechniquesByCategory("RedTeam")
	if len(rt) < 5 {
		t.Errorf("Expected at least 5 RedTeam techniques, got %d", len(rt))
	}
}
