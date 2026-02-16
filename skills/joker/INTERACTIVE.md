# joker Interactive Mode

**Launch an interactive REPL shell for Sims DBPF parsing and exploration.**

## Quick Start

```bash
# Launch interactive mode
./bin/joker

# Or explicitly
./bin/joker interactive
./bin/joker -i
```

## Interactive Commands

### parse `<file>`
Analyze and display detailed information about a Sims package file.

```
joker> parse ~/Documents/TheSims3/Saves/UserSaveGame.sims3pack

=== Sims Package Analysis ===

File: UserSaveGame.sims3pack
Game Version: Sims 3
DBPF Version: 2.0
Total Resources: 1247
...
```

### list `<file>`
Display all resources in a package with metadata in table format.

```
joker> list game.package

Type       Group      ID           Size       Compressed
0x043bec01 0x00000001 0x000000012a 8192       Yes
0x0210dc99 0x00000002 0x000000013b 4096       No
...
```

### info `<directory>`
Scan a directory recursively for all Sims save files.

```
joker> info ~/Documents/TheSims3/Saves/

~/Documents/TheSims3/Saves/UserSaveGame1.sims3pack
  Game: Sims 3
  Resources: 1247

~/Documents/TheSims3/Saves/UserSaveGame2.sims3pack
  Game: Sims 3
  Resources: 892
```

### extract `<file>` `<type>`
Extract resources of a specific type (future implementation).

```
joker> extract game.package 0x043bec01
Extracting resources of type 0x043bec01...
```

### help
Display available commands and examples.

```
joker> help
```

### quit / exit
Exit interactive mode.

```
joker> quit
```

## Session Examples

### Example 1: Analyze Multiple Saves

```
joker> parse ~/Saves/save1.sims3pack
=== Sims Package Analysis ===
Game Version: Sims 3
Total Resources: 1247

joker> parse ~/Saves/save2.sims3pack
=== Sims Package Analysis ===
Game Version: Sims 3
Total Resources: 892

joker> quit
Goodbye!
```

### Example 2: Explore Package Contents

```
joker> list game.package
Type       Group      ID           Size       Compressed
0x043bec01 0x00000001 0x000000012a 8192       Yes
0x0210dc99 0x00000002 0x000000013b 4096       No
0x0215ca48 0x00000003 0x000000014c 16384      Yes
...

joker> quit
```

### Example 3: Batch Directory Scan

```
joker> info ~/Documents/TheSims3/Saves/
Scanning directory: ~/Documents/TheSims3/Saves/

~/Documents/TheSims3/Saves/UserSaveGame1.sims3pack
  Game: Sims 3
  Resources: 1247

~/Documents/TheSims3/Saves/UserSaveGame2.sims3pack
  Game: Sims 3
  Resources: 892

joker> quit
Goodbye!
```

## Architecture

The interactive shell provides a REPL (Read-Eval-Print Loop) interface:

1. **Read**: User input from terminal
2. **Eval**: Parse and execute joker command
3. **Print**: Display results
4. **Loop**: Return to prompt

### Command Processing

```
User Input → Parse Command → Execute Handler → Display Output → Prompt
                ↓
           Unknown Command → Show Error → Prompt
```

## Implementation Details

The interactive mode is implemented in `interactive.go`:

- `StartInteractiveShell()` - Main REPL loop
- `handleInteractiveCommand()` - Command dispatcher
- `printInteractiveHelp()` - Help text generator

Commands are dispatched to existing handlers:
- `parseCmd()` - Parse command
- `listCmd()` - List command
- `infoCmd()` - Info command
- `extractCmd()` - Extract command

## Error Handling

Invalid commands are caught and displayed:

```
joker> invalid_command
Unknown command: invalid_command (type 'help' for commands)
joker>
```

Missing arguments are reported:

```
joker> parse
Usage: parse <file>
joker>
```

## Performance

Interactive mode has minimal overhead:
- Each command executes with same performance as CLI
- No state persistence between commands
- Immediate execution and feedback

## Integration with Boxxy

The interactive shell integrates with Boxxy's skill system:
- Each command invokes the underlying parser library
- Results displayed in real-time
- GF(3) validation performed transparently

## Exit Status

Interactive mode can be exited with:
- `quit` command
- `exit` command
- Ctrl+D (EOF)

Returns exit code 0 on successful exit.

## Future Enhancements

Planned interactive mode improvements:
- Command history and tab completion
- Batch command files (`.joker` scripts)
- Diff command for comparing saves
- Export command for format conversion
- Watch command for monitoring changes
- Config command for settings

## Examples in Scripts

Use joker interactively in scripts:

```bash
#!/bin/bash
{
    echo "info ~/Saves/"
    echo "parse ~/Saves/game.sims3pack"
    echo "quit"
} | /path/to/joker
```

## Troubleshooting

**No prompt appears:**
- Ensure terminal supports REPL mode
- Check file permissions on joker binary

**Commands not executing:**
- Type `help` to see available commands
- Ensure correct file paths

**File not found:**
- Verify file path is correct
- Use absolute paths for clarity

## See Also

- `joker parse` - Parse command documentation
- `joker list` - List command documentation
- `joker info` - Info command documentation
