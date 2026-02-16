// Skill integration for sqlite-scanner
package sqlite_scanner

import (
	"encoding/json"
)

// SQLiteScannerSkill represents the sqlite-scanner as a Boxxy skill
type SQLiteScannerSkill struct {
	Name         string
	Description  string
	Version      string
	Capabilities []string
	GF3Trit      int // -1 for validator, 0 for coordinator, +1 for generator
}

// NewSQLiteScannerSkill creates a new sqlite-scanner skill
func NewSQLiteScannerSkill() *SQLiteScannerSkill {
	return &SQLiteScannerSkill{
		Name:        "sqlite-scanner",
		Description: "Scan filesystems for SQLite databases by magic-byte detection",
		Version:     "0.1.1",
		Capabilities: []string{
			"scan-directories",
			"detect-sqlite",
			"json-output",
			"jsonl-output",
			"size-reporting",
		},
		GF3Trit: -1, // Verifier role
	}
}

// MarshalJSON converts the skill to JSON
func (s *SQLiteScannerSkill) MarshalJSON() ([]byte, error) {
	return json.MarshalIndent(map[string]interface{}{
		"name":         s.Name,
		"description":  s.Description,
		"version":      s.Version,
		"capabilities": s.Capabilities,
		"gf3_trit":     s.GF3Trit,
		"role":         "verifier",
		"upstream":     "github.com/simonw/sqlite-scanner",
		"detection":    "SQLite format 3\\x00 (16-byte magic header)",
		"invocation": []string{
			"uvx sqlite-scanner",
			"go run github.com/simonw/sqlite-scanner@latest",
		},
	}, "", "  ")
}

// Manifest returns the skill manifest for Boxxy
func (s *SQLiteScannerSkill) Manifest() map[string]interface{} {
	return map[string]interface{}{
		"skill_id":      "sqlite-scanner",
		"skill_name":    s.Name,
		"skill_version": s.Version,
		"description":   s.Description,
		"author":        "Simon Willison (upstream), boxxy (integration)",
		"license":       "Apache-2.0",
		"tags": []string{
			"scanner",
			"sqlite",
			"forensics",
			"filesystem",
			"magic-bytes",
			"detection",
		},
		"capabilities": s.Capabilities,
		"gf3_balance": map[string]interface{}{
			"trit":                        s.GF3Trit,
			"role":                        -1, // Verifier
			"contributes_to_conservation": true,
		},
		"integrations": []string{
			"joker-activity",
			"boxxy-skill-system",
			"uvx-runner",
		},
	}
}
