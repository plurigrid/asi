---
name: flox
description: Reproducible development environments powered by Nix.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# flox

Reproducible development environments powered by Nix.

**Repository**: https://github.com/flox/flox
**Documentation**: https://flox.dev/docs
**FloxHub**: https://hub.flox.dev

---

## Overview

Flox provides declarative, reproducible development environments using Nix as the package backend. Environments are defined in `manifest.toml` and can be shared via FloxHub.

```
.flox/
├── env/
│   └── manifest.toml    # Environment definition
├── env.json             # Environment metadata
└── env.lock             # Lockfile
```

---

## Installation

```bash
# macOS
brew install flox/flox/flox

# Linux
curl -fsSL https://downloads.flox.dev/by-env/stable/install | bash
```

---

## CLI Commands

### Environment Management

```bash
flox init                    # Create new environment
flox init -n myenv           # Named environment
flox init --auto-setup       # Auto-detect languages

flox activate                # Enter environment
flox activate -d ./path      # Activate in directory
flox activate -r user/env    # Activate remote environment

flox edit                    # Edit manifest.toml
flox edit -n newname         # Rename environment

flox delete                  # Delete environment
```

### Package Management

```bash
flox search ripgrep          # Search packages
flox show ripgrep            # Package details
flox install ripgrep         # Install package
flox uninstall ripgrep       # Remove package
flox list                    # List installed packages
flox upgrade                 # Upgrade packages
flox update                  # Update catalog
```

### Sharing (FloxHub)

```bash
flox auth login              # OAuth2 login
flox auth logout             # Remove token
flox auth status             # Check login status

flox push                    # Push to FloxHub
flox push --force            # Overwrite remote
flox pull user/env           # Pull from FloxHub
flox pull --force            # Overwrite local

flox envs                    # List environments
