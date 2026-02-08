# qigong: Migration from Homebrew to Pure Nix (via Flox)

## Overview

The new `flox-qigong-pure-nix.toml` replaces all Homebrew dependencies with Nix packages, providing:

- **Reproducible builds**: Same environment on any macOS machine
- **No system pollution**: No `/opt/homebrew` overhead
- **Cleaner isolation**: All tools sandboxed in Flox environment
- **Faster activation**: Flox caching layer speeds up startup
- **Better ARM64 support**: Nix nixpkgs better maintained for Apple Silicon

---

## File Comparison

| Component | Old (homebrew) | New (pure nix) |
|-----------|---|---|
| `flox-qigong.toml` | Mixed homebrew sources | `flox-qigong-pure-nix.toml` - pure nixpkgs |
| System tools | Requires homebrew install | Detected from `/usr/bin` (built-in) |
| Python | `homebrew:python@3.10` | `nixpkgs#python312` |
| Asitop | `homebrew:asitop` | Via `pip install asitop` (in venv) |
| Go | `homebrew:go` | `nixpkgs#go` |
| DuckDB | `homebrew:duckdb` | `nixpkgs#duckdb` |
| Total packages | 25 (many from homebrew) | 22 (all nixpkgs, optimized) |

---

## Migration Path

### Step 1: Switch to Pure Nix Configuration

```bash
# Backup old config
cp ~/.config/flox/environments/qigong/flox.toml \
   ~/.config/flox/environments/qigong/flox.toml.backup

# Use new pure-nix config
cp /Users/bob/ies/music-topos/flox-qigong-pure-nix.toml \
   ~/.config/flox/environments/qigong/flox.toml

# Or activate directly from the repo
cd /Users/bob/ies/music-topos
flox activate -d flox-qigong-pure-nix.toml
```

### Step 2: Rebuild Nix Environment

```bash
# Clear old environment
flox remove qigong

# Create new pure-nix environment
flox init -n qigong -d flox-qigong-pure-nix.toml

# Verify
flox list -e qigong
```

### Step 3: Install Optional Python Tools

```bash
# Activate environment
flox activate

# Install monitoring tools via pip (in isolated venv)
qigong install-python-tools

# Or manually:
pip install asitop psutil pandas
```

### Step 4: Verify System Tools

```bash
# System tools are auto-detected from /usr/bin
flox scripts status

# Should show:
# ✓ powermetrics (system)
# ✓ taskpolicy (system)
# ✓ dtrace (system)
# ✓ Instruments.app (Xcode)
```

---

## What Changed

### Removed (No Longer Needed)

```toml
# OLD: homebrew-based packages
[[package]]
name = "asitop"
source = "github:tlkh/asitop"

[[package]]
name = "metasploit"
source = "homebrew:metasploit"  # Removed: too large, rarely used

[[package]]
name = "google-santa"
source = "homebrew:google-santa"  # Removed: use system osquery instead
```

### Added (Nix Optimization)

```toml
# NEW: Direct nixpkgs references
[[package]]
name = "python312"
description = "Python 3.12 for monitoring scripts"
package = "nixpkgs#python312"

[[package]]
name = "duckdb"
description = "DuckDB for temporal analysis"
package = "nixpkgs#duckdb"

# ... all packages now reference nixpkgs#<package>
```

### System Tools (Unchanged)

These are **already on your macOS**, so no package needed:

```
✓ /usr/bin/powermetrics  (built-in energy monitoring)
✓ /usr/sbin/taskpolicy   (built-in QoS steering)
✓ /usr/sbin/dtrace       (built-in dynamic tracing)
✓ Instruments.app        (built-in profiling, in Xcode)
✓ Activity Monitor.app   (built-in resource monitoring)
✓ Console.app            (built-in log viewer)
```

---

## Benefits of Pure Nix

### 1. Reproducibility
```bash
# Same flox.toml = same environment everywhere
# No version drift from homebrew updates
# Works on M1, M2, M3 identically
```

### 2. No System Pollution
```bash
# Homebrew installs to /opt/homebrew
ls /opt/homebrew/bin  # 200+ tools polluting PATH

# Flox isolates everything
flox activate
echo $PATH  # Only includes flox packages
```

### 3. Faster Activation
```bash
# First time (downloads nix packages):
time flox activate  # ~15 seconds

# Subsequent (uses cache):
time flox activate  # ~2 seconds

# Homebrew (always installs from cache):
time brew install duckdb  # ~5 seconds
```

### 4. Better Python Isolation
```toml
# Old (homebrew python, global site-packages)
[[package]]
name = "py310"
source = "homebrew:python@3.10"

# New (isolated venv per project)
[[package]]
name = "python312"
package = "nixpkgs#python312"

# In environment:
python3 -m venv ~/.qigong/venv
source ~/.qigong/venv/bin/activate
pip install asitop  # Isolated from system Python
```

### 5. ARM64-Native Compilation
```bash
# Nix builds all packages for ARM64 (aarch64-darwin)
# Homebrew sometimes lags on M-series support

# Verify:
flox activate
file $(which python3)
# Should show: Mach-O 64-bit executable arm64
```

---

## Usage After Migration

### Activate Environment
```bash
flox activate -d ~/.config/flox/environments/qigong/flox.toml
# Or if installed in ~/.flox/environments/qigong:
flox activate -e qigong
```

### Run Scripts
```bash
# All available via 'flox scripts' or 'qigong' alias
flox scripts setup
flox scripts monitor-cores
flox scripts monitor-power
flox scripts install-python-tools
flox scripts analyze-resources
```

### Python Development
```bash
# Nix Python environment
python3 -c "import numpy; print(numpy.__version__)"

# Or interactive
python3
>>> import pandas as pd
>>> pd.__version__
'2.x.x'

# To install custom packages:
pip install <package>  # Installs to ~/.qigong/venv
```

### System Tool Integration
```bash
# System tools auto-available (no installation needed)
powermetrics -n 1
taskpolicy -b -p <pid>
dtrace -n 'syscall:::entry { @[execname] = count(); }'
```

---

## Troubleshooting Migration

### Issue: "Package not found" after switching

**Solution**: Clear Flox cache and rebuild
```bash
flox remove qigong
flox init -n qigong -d flox-qigong-pure-nix.toml
flox activate
```

### Issue: "python3 not found" in scripts

**Solution**: Ensure Python is in Flox environment
```bash
# In activated environment:
which python3
# Should show: ~/.flox/environments/qigong/...

# If not:
flox search python3
flox install python312
```

### Issue: "asitop: command not found"

**Solution**: Install via pip in environment
```bash
flox activate
pip install asitop
asitop
```

### Issue: System tools not available in Flox

**Solution**: They're in `/usr/bin`, auto-added to PATH
```bash
flox activate
powermetrics --version
# If not found:
export PATH="/usr/bin:/usr/sbin:$PATH"
powermetrics --version
```

---

## Comparison: Old vs. New Workflows

### Old Workflow (Homebrew)
```bash
# Install globally via homebrew
brew install python@3.10 duckdb go lldb

# Everything in /opt/homebrew/bin (pollutes PATH)
which python3
# /opt/homebrew/bin/python3

# Activation simple but no isolation
flox activate
```

### New Workflow (Pure Nix)
```bash
# Packages defined in flox.toml
# Nothing installed globally

# Only available in Flox environment
flox activate
which python3
# ~/.flox/environments/qigong/.../python3

# Python isolated in venv
pip install asitop
# Installed to ~/.qigong/venv only
```

---

## File Organization After Migration

```
~/.config/flox/
├── environments/
│   └── qigong/
│       ├── flox.toml            (pure nix config)
│       └── .flox.lock           (lock file)

~/.flox/
└── environments/
    └── qigong/                  (cached nix packages)
        ├── bin/                 (symlinks to nix tools)
        ├── lib/                 (libraries)
        └── share/               (data files)

~/.qigong/
├── logs/                         (runtime logs)
├── data/                         (baseline metrics)
├── venv/                         (python virtual env)
└── reports/                      (engagement reports)
```

---

## Advanced: Building Custom Flox Environment

If you want to add packages beyond what's in pure-nix:

```bash
# Create custom environment
flox init -d my-qigong.toml

# Edit and add packages
cat >> my-qigong.toml << 'EOF'
[[package]]
name = "custom-tool"
package = "nixpkgs#custom-tool"
EOF

# Activate
flox activate -d my-qigong.toml
```

---

## References

- [Flox Documentation](https://flox.dev/docs/)
- [Nixpkgs Search](https://search.nixos.org/packages)
- [macOS Nix Installation](https://nixos.org/manual/nix/stable/installation/installing-binary.html#macos)
- [Nix Package Search](https://package.elm-lang.org/)

---

## Summary

**Old approach (Homebrew):**
- ❌ System-wide pollution (`/opt/homebrew`)
- ❌ Version drift across machines
- ❌ Manual dependency management
- ✓ Familiar to macOS users

**New approach (Pure Nix via Flox):**
- ✓ Isolated per-environment
- ✓ Reproducible configurations
- ✓ Version pinning (lock file)
- ✓ ARM64 optimized
- ✓ Faster activation (caching)

**Recommendation**: Use `flox-qigong-pure-nix.toml` for new installations and migration.
