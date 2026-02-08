---
name: storage-reclaim
description: Rapidly find and reclaim disk storage by identifying build artifacts, git garbage, temp files, and other space hogs. Use when disk is full or running low on space.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Storage Reclaim

Rapid parallel investigation and cleanup of disk storage.

## Quick Start

```bash
# Top-level overview
du -sh /path/*/ 2>/dev/null | sort -hr | head -20

# Drill into specific directory
du -sh /path/subdir/*/ 2>/dev/null | sort -hr | head -15
```

## Common Space Hogs

### 1. Rust Build Artifacts (`target/`)
- Location: Any Rust project root
- Size: 1-10+ GB per project
- Safe to delete: Yes (rebuilds on next `cargo build`)

```bash
# Find all Rust target directories
find ~ -type d -name "target" -exec du -sh {} \; 2>/dev/null | sort -hr | head -20

# Clean specific project
rm -rf /path/to/project/target

# Or use cargo
cd /path/to/project && cargo clean
```

### 2. Git Garbage (tmp_pack files)
- Location: `.git/objects/pack/tmp_pack_*`
- Cause: Interrupted git operations
- Size: Can be gigabytes

```bash
# Check for git garbage
git count-objects -vH
# Look for "size-garbage" line

# Remove stale pack files
rm -f .git/objects/pack/tmp_pack_*

# Verify cleanup
git count-objects -vH
```

### 3. Node Modules
- Location: `node_modules/` in JS projects
- Size: 100MB - 2GB per project

```bash
# Find all node_modules
find ~ -type d -name "node_modules" -prune -exec du -sh {} \; 2>/dev/null | sort -hr

# Remove (can reinstall with npm install)
rm -rf /path/to/project/node_modules
```

### 4. Python Virtual Environments
- Location: `.venv/`, `venv/`, `env/`
- Size: 100MB - 1GB per environment

```bash
find ~ -type d \( -name ".venv" -o -name "venv" -o -name "env" \) -exec du -sh {} \; 2>/dev/null | sort -hr
```

### 5. Hidden Temp Directories
- Location: `.tmp/`, `.cache/`, `__pycache__/`
- Often overlooked by `du` on directories

```bash
# Check hidden dirs specifically
du -sh /path/.* 2>/dev/null | sort -hr | head -10
```

### 6. Julia Artifacts
- Location: `~/.julia/artifacts/`, `~/.julia/compiled/`
- Size: Can grow to many GB

```bash
du -sh ~/.julia/*/ 2>/dev/null | sort -hr
```

### 7. Docker
```bash
docker system df
docker system prune -a  # Remov