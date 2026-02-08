---
name: zls-integration
description: "zls-integration skill"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ZLS Integration Skill

Zig Language Server (ZLS) provides IDE features for Zig development. This skill covers installation, configuration, build-on-save diagnostics, and troubleshooting.

## Quick Reference

| Feature | ZLS Support | Notes |
|---------|-------------|-------|
| Autocomplete | ✓ Full | Includes comptime-aware completion |
| Goto Definition | ✓ Full | Cross-file navigation |
| Find References | ✓ Full | All usages in workspace |
| Hover Documentation | ✓ Full | Inline docs from source |
| Diagnostics | ⚡ Parser-level | Semantic via build-on-save |
| Rename Symbol | ✓ Full | Safe refactoring |
| Code Actions | ✓ Partial | Fix imports, remove unused |
| Formatting | ✓ Full | Uses `zig fmt` |

## Installation

### Via Package Manager (Recommended)

```bash
# macOS (Homebrew)
brew install zls

# Nix/Flox
flox install zls

# Arch Linux
pacman -S zls

# From source (any platform)
git clone https://github.com/zigtools/zls
cd zls
zig build -Doptimize=ReleaseSafe
```

### Version Compatibility

| Zig Version | ZLS Version | Notes |
|-------------|-------------|-------|
| 0.15.x | 0.15.x | Current stable |
| 0.14.x | 0.14.x | Previous stable |
| 0.13.x | 0.13.x | Legacy |
| master | master | Build from source |

**Always match ZLS version to Zig version.**

## Configuration

### zls.json Location

```
~/.config/zls.json           # Linux/macOS
%APPDATA%\zls.json           # Windows
<project>/.zls.json          # Project-specific
```

### Essential Configuration

```json
{
  "zig_exe_path": "/path/to/zig",
  "enable_autofix": true,
  "enable_import_access": true,
  "highlight_global_var_declarations": true,
  "warn_style": true,
  "enable_build_on_save": true,
  "build_on_save_step": "check"
}
```

## Build-On-Save Diagnostics

ZLS can run your build script on save to catch semantic errors (type mismatches, wrong argument counts) that parser-level analysis misses.

### Step 1: Add Check Step to build.zig

```zig
// build.zig
pub fn build(b: *std.Build) void {
 