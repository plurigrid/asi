# UREPL Claude Code Skill Setup Guide

**Status**: Ready for Installation ✅
**Version**: 0.2.0
**Installation Methods**: 3 options available

---

## Quick Start (Recommended)

### Option 1: Direct CLI Usage (No Installation Required)

Use the UREPL CLI directly from the music-topos directory:

```bash
# From music-topos directory
node bin/urepl.js execute scheme "(+ 1 2 3)" 42
node bin/urepl.js bootstrap
node bin/urepl.js status
```

Or create a symlink for global access:

```bash
# Create symlink (no permissions required)
ln -s "$(pwd)/bin/urepl.js" ~/.local/bin/urepl
chmod +x ~/.local/bin/urepl

# Now use globally
urepl execute scheme "(+ 1 2 3)"
```

### Option 2: NPM Installation (Local Development)

```bash
cd /Users/bob/ies/music-topos
npm install

# Test locally
npx urepl --version
npx urepl execute scheme "(+ 1 2 3)"
```

### Option 3: Claude Code Skill Configuration

Add to your Claude Code configuration:

**File**: `~/.claude/skills.json` (or `.claude/config.json`)

```json
{
  "skills": [
    {
      "name": "urepl",
      "type": "external",
      "command": "node /Users/bob/ies/music-topos/bin/urepl.js",
      "enabled": true,
      "description": "Execute code in Scheme, Clojure, or Common Lisp"
    }
  ]
}
```

Then use in Claude Code:

```bash
/urepl execute scheme "(+ 1 2 3)" 42
/urepl bootstrap
/urepl load-srfi 26
```

---

## Installation Methods Detailed

### Method 1: Direct Node Execution (Simplest)

**Pros**: No installation, no permissions issues, works immediately
**Cons**: Requires full path or symlink

```bash
# Direct execution
node /Users/bob/ies/music-topos/bin/urepl.js execute scheme "(+ 1 2 3)"

# Via symlink
ln -s /Users/bob/ies/music-topos/bin/urepl.js /usr/local/bin/urepl
urepl execute scheme "(+ 1 2 3)"
```

### Method 2: NPM Local Install

**Pros**: Standard npm workflow, works in the project directory
**Cons**: Requires npm, local only

```bash
cd /Users/bob/ies/music-topos

# Install dependencies (if not already done)
npm install

# Test
npx urepl --version
npx urepl execute scheme "(+ 1 2 3)"

# Or run scripts
npm run test:connectors
npm run test:bootstrap
```

### Method 3: Claude Code Skill Registration

**Pros**: Integrated with Claude Code, use `/urepl` commands
**Cons**: Requires Claude Code configuration

**Step 1**: Create skill configuration file

```bash
mkdir -p ~/.claude/skills
cat > ~/.claude/skills/urepl.json << 'EOF'
{
  "name": "urepl",
  "description": "Universal REPL Protocol - Execute code in Scheme/Clojure/Lisp",
  "version": "0.2.0",
  "author": "Music-Topos",
  "commands": [
    {
      "name": "execute",
      "description": "Execute code through UREPL coordinator",
      "usage": "/urepl execute <dialect> <code> [seed]",
      "examples": [
        "/urepl execute scheme \"(+ 1 2 3)\" 42",
        "/urepl execute clojure \"(+ 1 2 3)\""
      ]
    },
    {
      "name": "bootstrap",
      "description": "Run UREPL bootstrap sequence",
      "usage": "/urepl bootstrap [seed]",
      "examples": [
        "/urepl bootstrap 42"
      ]
    },
    {
      "name": "load-srfi",
      "description": "Load a Scheme Request for Implementation",
      "usage": "/urepl load-srfi <number>",
      "examples": [
        "/urepl load-srfi 26"
      ]
    },
    {
      "name": "list-srfis",
      "description": "List available SRFIs",
      "usage": "/urepl list-srfis",
      "examples": [
        "/urepl list-srfis"
      ]
    },
    {
      "name": "status",
      "description": "Check UREPL server status",
      "usage": "/urepl status",
      "examples": [
        "/urepl status"
      ]
    }
  ],
  "implementation": {
    "type": "node",
    "entrypoint": "/Users/bob/ies/music-topos/bin/urepl.js",
    "requirements": {
      "node": ">=18.0.0",
      "npm": ">=9.0.0"
    }
  },
  "capabilities": [
    "execute-code",
    "multi-language",
    "color-guided",
    "repl-management"
  ]
}
EOF
```

**Step 2**: Register with Claude Code

```bash
# Tell Claude Code about the skill
claude code register-skill ~/.claude/skills/urepl.json
```

**Step 3**: Use in Claude Code

```bash
# Now these commands work
/urepl execute scheme "(+ 1 2 3)"
/urepl bootstrap
/urepl status
```

---

## Usage Examples

### Example 1: Execute Scheme Code

```bash
$ /urepl execute scheme "(define fib (lambda (n) (if (<= n 1) 1 (+ (fib (- n 1)) (fib (- n 2))))))" 42

🎨 UREPL Execute
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

ℹ Dialect: scheme
ℹ Code: (define fib ...)
ℹ Seed: 42

✓ Execution completed

Result:
{
  "success": true,
  "value": "fib",
  "color": "#FF6B35",
  "duration_ms": 145
}
```

### Example 2: Run Bootstrap Sequence

```bash
$ /urepl bootstrap

🎨 UREPL Bootstrap Sequence
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

ℹ Seed: 42

Bootstrap steps:
  ✓ Initialize Scheme REPL [#FF6B35]
  ✓ Initialize Clojure REPL [#F7931E]
  ✓ Initialize Common Lisp REPL [#FBB03B]
  ✓ Set UREPL Version (Scheme) [#009CA3]
  ✓ Set UREPL Version (Clojure) [#7B68EE]
  ✓ Set UREPL Version (Common Lisp) [#FF1493]
  ✓ Load SRFI 2 (List Predicates) [#00CED1]
  ✓ Load SRFI 5 (Let Syntax) [#32CD32]
  ✓ Load SRFI 26 (Cut/Cute) [#FFD700]
  ✓ Load SRFI 48 (Formatted Output) [#FF6347]
  ✓ Self-Host UREPL Evaluator [#DC143C]
  ✓ Enable Color-Guided Execution [#FF69B4]

✓ Bootstrap complete: 12/12
```

### Example 3: Load SRFI

```bash
$ /urepl load-srfi 26

🎨 Load SRFI
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

ℹ Loading SRFI 26

✓ SRFI 26 loaded: Cut/Cute (Partial Application)

Provides:
  • cut
  • cute
  • <>
  • <...>
```

---

## Setup Verification

### Verify Installation

```bash
# Check Node is available
node --version
# Should output: v18.0.0 or higher

# Check npm is available
npm --version
# Should output: 9.0.0 or higher

# Check UREPL files
ls -la /Users/bob/ies/music-topos/bin/urepl.js
ls -la /Users/bob/ies/music-topos/package.json

# Test direct execution
node /Users/bob/ies/music-topos/bin/urepl.js --version
# Should output: UREPL v0.2.0
```

### Test Each Command

```bash
# Test execute
node bin/urepl.js execute scheme "(+ 1 2)"

# Test bootstrap
node bin/urepl.js bootstrap

# Test list-srfis
node bin/urepl.js list-srfis

# Test status
node bin/urepl.js status

# Test help
node bin/urepl.js help
```

---

## Troubleshooting

### Issue: "command not found: urepl"

**Solution**: Use full path or create symlink

```bash
# Option 1: Use full path
node /Users/bob/ies/music-topos/bin/urepl.js execute scheme "(+ 1 2)"

# Option 2: Create symlink
ln -s /Users/bob/ies/music-topos/bin/urepl.js ~/.local/bin/urepl
urepl execute scheme "(+ 1 2)"

# Option 3: Add to PATH
export PATH="/Users/bob/ies/music-topos/bin:$PATH"
urepl execute scheme "(+ 1 2)"
```

### Issue: "Permission denied"

**Solution**: Make script executable

```bash
chmod +x /Users/bob/ies/music-topos/bin/urepl.js
chmod +x /Users/bob/ies/music-topos/bin/urepl-server.js
```

### Issue: Claude Code doesn't recognize /urepl command

**Solution**: Check skill registration

```bash
# Verify skill configuration
cat ~/.claude/skills/urepl.json

# Check Claude Code version
claude --version

# Restart Claude Code
# Then try: /urepl execute scheme "(+ 1 2)"
```

### Issue: REPL connections failing

**Solution**: Ensure REPL backends are running

```bash
# Terminal 1: Scheme REPL
racket
(require (planet neil/geiser:1:2))

# Terminal 2: Clojure REPL
clojure -Sdeps '{:deps {nrepl/nrepl {:mvn/version "0.8.3"}}}'

# Terminal 3: Common Lisp REPL
sbcl
(require 'swank)
(swank:create-server)

# Then test
node bin/urepl.js status
```

---

## Integration with Music-Topos

### As a World Skill

Add to your music-topos world configuration:

```python
# In worlds/urepl_world.py
from worlds.base import World

class UReplWorld(World):
    """Execute UREPL code through live REPLs"""

    def __init__(self, name="urepl"):
        super().__init__(name)
        self.server_url = "http://localhost:8765"

    def execute_scheme(self, code: str, seed: int = 42):
        """Execute Scheme code with color guidance"""
        return self.execute("scheme", code, seed)

    def execute_clojure(self, code: str, seed: int = 42):
        """Execute Clojure code with color guidance"""
        return self.execute("clojure", code, seed)

    def execute_lisp(self, code: str, seed: int = 42):
        """Execute Common Lisp code with color guidance"""
        return self.execute("lisp", code, seed)

    def execute(self, dialect: str, code: str, seed: int = 42):
        """Generic execute method"""
        import subprocess
        result = subprocess.run(
            ["node", "bin/urepl.js", "execute", dialect, code, str(seed)],
            capture_output=True,
            text=True
        )
        return result.stdout
```

### Register in Worlds Manager

```python
# In worlds/__init__.py
from worlds.urepl_world import UReplWorld

worlds = {
    "urepl": UReplWorld(),
    # ... other worlds
}
```

### Use in Agents

```python
agent = Agent(name="researcher")
result = agent.execute_in_world("urepl", """
(define solve-puzzle
  (lambda (puzzle)
    (display "Solving: ")
    (display puzzle)
    (newline)))

(solve-puzzle "prime-factorization")
""")
```

---

## Next Steps

### 1. Choose Installation Method

- **Option 1** (Simplest): Direct node execution with symlink
- **Option 2** (Standard): NPM local installation
- **Option 3** (Best UX): Claude Code skill registration

### 2. Test Installation

```bash
# Run the test target
just urepl-phase2-test

# Or test manually
node bin/urepl.js execute scheme "(+ 1 2 3)"
```

### 3. Start Using

```bash
# Execute code
/urepl execute scheme "(+ 1 2 3)"

# Bootstrap system
/urepl bootstrap

# Check status
/urepl status
```

### 4. Advanced Usage

- Deploy server: `urepl server 8765`
- Load SRFIs: `urepl load-srfi 26`
- Use in worlds: See integration section above

---

## Support & Documentation

**Full Guides**:
- Installation: This file
- Usage: README_UREPL_SKILL.md
- Architecture: UREPL_MASTER_INDEX.md
- Phase 2 Details: UREPL_PHASE2_SELFHOSTING.md

**Quick Commands**:
```bash
node bin/urepl.js help              # Show all commands
node bin/urepl.js --version         # Show version
node bin/urepl.js status            # Check server status
```

---

**Ready to use!** Choose your installation method above and start executing code. 🚀
