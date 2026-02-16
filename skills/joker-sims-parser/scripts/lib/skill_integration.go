// Skill integration for Sims parser
package sims_parser

import (
	"encoding/json"
)

// SimsParserSkill represents the Sims parser as a Boxxy skill
type SimsParserSkill struct {
	Name        string
	Description string
	Version     string
	Capabilities []string
	GF3Trit     int // -1 for validator, 0 for coordinator, +1 for generator
}

// NewSimsParserSkill creates a new Sims parser skill
func NewSimsParserSkill() *SimsParserSkill {
	return &SimsParserSkill{
		Name:        "sims-parser",
		Description: "Parse and extract data from Sims 2/3/4 DBPF package files",
		Version:     "1.0.0",
		Capabilities: []string{
			"parse-dbpf",
			"list-resources",
			"detect-sims-version",
			"extract-resource",
			"scan-saves",
		},
		GF3Trit: -1, // Validator role
	}
}

// MarshalJSON converts the skill to JSON
func (s *SimsParserSkill) MarshalJSON() ([]byte, error) {
	return json.MarshalIndent(map[string]interface{}{
		"name":         s.Name,
		"description":  s.Description,
		"version":      s.Version,
		"capabilities": s.Capabilities,
		"gf3_trit":     s.GF3Trit,
		"role":         "validator",
		"supported_games": []string{
			"The Sims 2",
			"The Sims 3",
			"The Sims 4",
		},
		"supported_formats": []string{
			".sims",
			".sims2",
			".package",
			".sims3pack",
			".ts4script",
		},
	}, "", "  ")
}

// Manifest returns the skill manifest for Boxxy
func (s *SimsParserSkill) Manifest() map[string]interface{} {
	return map[string]interface{}{
		"skill_id":      "sims-parser",
		"skill_name":    s.Name,
		"skill_version": s.Version,
		"description":   s.Description,
		"author":        "boxxy",
		"license":       "MIT",
		"tags": []string{
			"parser",
			"sims",
			"dbpf",
			"games",
			"reverse-engineering",
		},
		"capabilities": s.Capabilities,
		"gf3_balance": map[string]interface{}{
			"trit":      s.GF3Trit,
			"role":      -1, // Validator
			"contributes_to_conservation": true,
		},
		"integrations": []string{
			"joker-cli",
			"boxxy-skill-system",
		},
	}
}

// SkillMarkdown returns SKILL.md content for the skill registry
func SkillMarkdown() string {
	return `# sims-parser - Sims DBPF Parser Skill

## Overview

Comprehensive parser for The Sims game package files across all generations (Sims 2, 3, 4). Provides DBPF format validation, resource extraction, and metadata analysis.

## Capabilities

- parse-dbpf: Parse and validate DBPF package structure
- list-resources: Enumerate all resources in a package with metadata
- detect-sims-version: Identify game version from DBPF format
- extract-resource: Extract individual resources by type/group/ID
- scan-saves: Recursively scan directories for Sims save files

## Supported Formats

Game: The Sims 2, Extension: .sims/.sims2, DBPF Version: 1.0-1.1, Compression: QFS/RefPack
Game: The Sims 3, Extension: .package/.sims3pack, DBPF Version: 2.0, Compression: QFS/RefPack
Game: The Sims 4, Extension: .package/.ts4script, DBPF Version: 2.0, Compression: ZLIB

## GF(3) Role

Trit: -1 (MINUS)
Role: Validator
Responsibility: DBPF format validation and resource verification

## Usage

joker parse <file>         - Analyze package structure
joker list <file>          - List all resources
joker info <directory>     - Scan for Sims saves

## Integration

Accessible via:
- joker CLI tool
- Boxxy skill system
- Internal sims_parser package

## License: MIT
## Author: boxxy team
`
}
