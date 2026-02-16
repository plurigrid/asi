// Interactive REPL shell for joker
package main

import (
	"bufio"
	"fmt"
	"os"
	"strings"
)

// StartInteractiveShell launches an interactive REPL for joker commands
func StartInteractiveShell() {
	fmt.Println(`╔═══════════════════════════════════════════════════════════════╗
║                    joker - Interactive Mode                      ║
║              Sims DBPF Parser for Boxxy Skill System             ║
╚═══════════════════════════════════════════════════════════════════╝

Type 'help' for commands, 'quit' to exit.`)

	reader := bufio.NewReader(os.Stdin)

	for {
		fmt.Print("joker> ")
		input, err := reader.ReadString('\n')
		if err != nil {
			break
		}

		input = strings.TrimSpace(input)
		if input == "" {
			continue
		}

		if !handleInteractiveCommand(input) {
			break
		}
	}

	fmt.Println("\nGoodbye!")
}

func handleInteractiveCommand(input string) bool {
	parts := strings.Fields(input)
	if len(parts) == 0 {
		return true
	}

	cmd := parts[0]

	switch cmd {
	case "help":
		printInteractiveHelp()
	case "quit", "exit":
		return false
	case "parse":
		if len(parts) < 2 {
			fmt.Println("Usage: parse <file>")
			return true
		}
		os.Args = append([]string{"joker", "parse"}, parts[1:]...)
		parseCmd(parts[1:])
	case "list":
		if len(parts) < 2 {
			fmt.Println("Usage: list <file>")
			return true
		}
		os.Args = append([]string{"joker", "list"}, parts[1:]...)
		listCmd(parts[1:])
	case "info":
		if len(parts) < 2 {
			fmt.Println("Usage: info <directory>")
			return true
		}
		os.Args = append([]string{"joker", "info"}, parts[1:]...)
		infoCmd(parts[1:])
	case "extract":
		if len(parts) < 3 {
			fmt.Println("Usage: extract <file> <type>")
			return true
		}
		os.Args = append([]string{"joker", "extract"}, parts[1:]...)
		extractCmd(parts[1:])
	default:
		fmt.Printf("Unknown command: %s (type 'help' for commands)\n", cmd)
	}

	return true
}

func printInteractiveHelp() {
	fmt.Println(`
Available commands:

  parse <file>           - Analyze a Sims package file structure
  list <file>            - List all resources in a package
  info <directory>       - Scan directory for Sims save files
  extract <file> <type>  - Extract resources by type
  help                   - Show this help message
  quit / exit            - Exit interactive mode

Examples:
  joker> parse ~/Documents/TheSims3/Saves/UserSaveGame.sims3pack
  joker> list game.package
  joker> info ~/Saves/`)
}
