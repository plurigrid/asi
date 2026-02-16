// joker: Sims save file parser and manager for Boxxy
// Wraps DBPF parsing for all Sims generations (2, 3, 4)
package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/bmorphism/boxxy/internal/sims_parser"
)

func main() {
	if len(os.Args) < 2 {
		StartInteractiveShell()
		return
	}

	cmd := os.Args[1]

	// Check for interactive flag
	if cmd == "interactive" || cmd == "-i" || cmd == "--interactive" {
		StartInteractiveShell()
		return
	}

	switch cmd {
	case "parse":
		parseCmd(os.Args[2:])
	case "list":
		listCmd(os.Args[2:])
	case "extract":
		extractCmd(os.Args[2:])
	case "info":
		infoCmd(os.Args[2:])
	default:
		fmt.Printf("Unknown command: %s\n", cmd)
		printUsage()
		os.Exit(1)
	}
}

func printUsage() {
	fmt.Fprintf(os.Stderr, `joker - Sims save file parser for Boxxy

Usage:
  joker parse <file>            Parse and analyze a Sims package file
  joker list <file>             List all resources in a Sims package
  joker extract <file> <type>   Extract specific resource type
  joker info <directory>        Scan directory for Sims saves

Examples:
  joker parse UserSaveGame.sims2
  joker list C001.package
  joker info ~/Documents/TheSims3/Saves/
`)
}

func parseCmd(args []string) {
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Usage: joker parse <file>\n")
		os.Exit(1)
	}

	filepath := args[0]
	file, err := os.Open(filepath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error opening file: %v\n", err)
		os.Exit(1)
	}
	defer file.Close()

	pkg, err := sims_parser.NewDBPFPackage(file)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing DBPF: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("=== Sims Package Analysis ===\n\n")
	fmt.Printf("File: %s\n", filepath)
	fmt.Printf("Game Version: %s\n", pkg.GameVersion())
	fmt.Printf("DBPF Version: %d.%d\n", pkg.Header.MajorVersion, pkg.Header.MinorVersion)
	fmt.Printf("Total Resources: %d\n", len(pkg.Resources))
	fmt.Printf("File Size: %d bytes\n\n", pkg.Header.FileSize)

	fmt.Printf("Index Information:\n")
	fmt.Printf("  Index Count: %d\n", pkg.Header.IndexCount)
	fmt.Printf("  Index Offset: 0x%08x\n", pkg.Header.IndexOffset)
	fmt.Printf("  Created: %d\n", pkg.Header.CreatedDate)
	fmt.Printf("  Modified: %d\n\n", pkg.Header.ModifiedDate)

	// Categorize resources by type
	typeMap := make(map[uint32]int)
	compressedCount := 0

	for _, res := range pkg.Resources {
		typeMap[res.ResourceType]++
		if res.Compressed != 0xFFFFFFFF {
			compressedCount++
		}
	}

	fmt.Printf("Resource Types Found:\n")
	for resType, count := range typeMap {
		fmt.Printf("  Type 0x%08x: %d resources\n", resType, count)
	}
	fmt.Printf("\nCompressed Resources: %d\n", compressedCount)
	fmt.Printf("Uncompressed Resources: %d\n", len(pkg.Resources)-compressedCount)
}

func listCmd(args []string) {
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Usage: joker list <file>\n")
		os.Exit(1)
	}

	file, err := os.Open(args[0])
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error opening file: %v\n", err)
		os.Exit(1)
	}
	defer file.Close()

	pkg, err := sims_parser.NewDBPFPackage(file)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing DBPF: %v\n", err)
		os.Exit(1)
	}

	summaries := pkg.ListResources()
	fmt.Printf("%-10s %-10s %-12s %-12s %s\n",
		"Type", "Group", "ID", "Size", "Compressed")
	fmt.Println(strings.Repeat("-", 60))

	for _, s := range summaries {
		compStr := "No"
		if s.IsCompressed {
			compStr = "Yes"
		}
		fmt.Printf("0x%08x 0x%08x 0x%12x %-12d %s\n",
			s.ResourceType, s.ResourceGroup, s.ResourceID, s.Size, compStr)
	}
}

func extractCmd(args []string) {
	if len(args) < 2 {
		fmt.Fprintf(os.Stderr, "Usage: joker extract <file> <type>\n")
		os.Exit(1)
	}
	fmt.Println("Extract command not yet implemented")
}

func infoCmd(args []string) {
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Usage: joker info <directory>\n")
		os.Exit(1)
	}

	dir := args[0]
	fmt.Printf("Scanning directory: %s\n\n", dir)

	err := filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if info.IsDir() {
			return nil
		}

		// Check for Sims files by extension
		ext := filepath.Ext(path)
		switch ext {
		case ".sims", ".sims2", ".package", ".sims3pack", ".ts4script":
			file, err := os.Open(path)
			if err != nil {
				return nil
			}
			defer file.Close()

			pkg, err := sims_parser.NewDBPFPackage(file)
			if err != nil {
				// Not a valid DBPF, skip
				return nil
			}

			fmt.Printf("%s\n", path)
			fmt.Printf("  Game: %s\n", pkg.GameVersion())
			fmt.Printf("  Resources: %d\n", len(pkg.Resources))
		}

		return nil
	})

	if err != nil {
		fmt.Fprintf(os.Stderr, "Error scanning directory: %v\n", err)
		os.Exit(1)
	}
}
