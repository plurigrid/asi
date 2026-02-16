// sqlite-scanner: Boxxy skill wrapper for simonw/sqlite-scanner
// Invokes the Go binary via uvx and processes results
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"strings"
)

// ScanEntry represents a discovered SQLite database
type ScanEntry struct {
	Path string `json:"path"`
	Size int64  `json:"size,omitempty"`
}

// ScanResult holds the full scan output
type ScanResult struct {
	Entries []ScanEntry `json:"entries"`
}

func main() {
	if len(os.Args) < 2 {
		printUsage()
		return
	}

	cmd := os.Args[1]

	switch cmd {
	case "scan":
		scanCmd(os.Args[2:])
	case "scan-json":
		scanJSONCmd(os.Args[2:])
	case "verify-canaries":
		verifyCanariesCmd(os.Args[2:])
	case "manifest":
		manifestCmd()
	default:
		fmt.Printf("Unknown command: %s\n", cmd)
		printUsage()
		os.Exit(1)
	}
}

func printUsage() {
	fmt.Fprintf(os.Stderr, `sqlite-scanner - Boxxy skill wrapper for simonw/sqlite-scanner

Usage:
  sqlite-scanner scan <dir> [<dir>...]          Scan directories (plain text)
  sqlite-scanner scan-json <dir> [<dir>...]     Scan directories (JSON output)
  sqlite-scanner verify-canaries <file> <dir>   Verify canary SQLite files exist
  sqlite-scanner manifest                       Print skill manifest

Requires: uvx (uv tool runner) with sqlite-scanner package

Examples:
  sqlite-scanner scan ~/Library
  sqlite-scanner scan-json ~/Documents ~/Desktop
  sqlite-scanner verify-canaries canaries.txt /tmp/honeypot
`)
}

func scanCmd(args []string) {
	if len(args) == 0 {
		args = []string{"."}
	}

	uvxArgs := append([]string{"sqlite-scanner", "--size"}, args...)
	cmd := exec.Command("uvx", uvxArgs...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr

	if err := cmd.Run(); err != nil {
		fmt.Fprintf(os.Stderr, "scan failed: %v\n", err)
		os.Exit(1)
	}
}

func scanJSONCmd(args []string) {
	if len(args) == 0 {
		args = []string{"."}
	}

	uvxArgs := append([]string{"sqlite-scanner", "--json", "--size"}, args...)
	cmd := exec.Command("uvx", uvxArgs...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr

	if err := cmd.Run(); err != nil {
		fmt.Fprintf(os.Stderr, "scan failed: %v\n", err)
		os.Exit(1)
	}
}

func verifyCanariesCmd(args []string) {
	if len(args) < 2 {
		fmt.Fprintf(os.Stderr, "Usage: sqlite-scanner verify-canaries <canary-list> <scan-dir>\n")
		os.Exit(1)
	}

	canaryFile := args[0]
	scanDir := args[1]

	// Read expected canary paths
	data, err := os.ReadFile(canaryFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to read canary list: %v\n", err)
		os.Exit(1)
	}
	expectedPaths := strings.Split(strings.TrimSpace(string(data)), "\n")

	// Run scanner and capture JSON output
	cmd := exec.Command("uvx", "sqlite-scanner", "--json", "--size", scanDir)
	output, err := cmd.Output()
	if err != nil {
		fmt.Fprintf(os.Stderr, "scan failed: %v\n", err)
		os.Exit(1)
	}

	var result ScanResult
	if err := json.Unmarshal(output, &result); err != nil {
		fmt.Fprintf(os.Stderr, "Failed to parse scan output: %v\n", err)
		os.Exit(1)
	}

	// Build set of found paths
	found := make(map[string]bool)
	for _, entry := range result.Entries {
		found[entry.Path] = true
	}

	// Verify each canary
	allPresent := true
	for _, expected := range expectedPaths {
		if expected == "" {
			continue
		}
		if found[expected] {
			fmt.Printf("  [OK] %s\n", expected)
		} else {
			fmt.Printf("  [MISSING] %s\n", expected)
			allPresent = false
		}
	}

	if allPresent {
		fmt.Println("\nAll canary databases verified.")
	} else {
		fmt.Println("\nWARNING: Some canary databases are missing!")
		os.Exit(1)
	}
}

func manifestCmd() {
	manifest := map[string]interface{}{
		"skill_id":   "sqlite-scanner",
		"skill_name": "sqlite-scanner",
		"version":    "0.1.1",
		"gf3_trit":   -1,
		"role":       "Verifier(-1)",
		"upstream":   "github.com/simonw/sqlite-scanner",
		"triad": map[string]string{
			"verifier":    "sqlite-scanner (-1)",
			"coordinator": "jo-clojure (0)",
			"generator":   "hy-regime (+1)",
		},
	}

	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	enc.Encode(manifest)
}
