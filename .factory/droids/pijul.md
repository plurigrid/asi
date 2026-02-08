---
name: pijul
description: Pijul patch-based VCS with categorical patch theory for skill versioning
model: inherit
tools: read-only
---

# pijul

Patch-based version control with mathematically sound commutative patch theory.

**Trit**: -1 (MINUS) - Validator role for patch verification and merge correctness

---

## Overview

Pijul is a distributed VCS where patches are first-class citizens that commute when independent. This maps directly to:
- **GF(3) skill derivation chains**: patches as morphisms between skill states
- **Pushouts = merges**: categorical semantics for conflict resolution
- **Sparsity preservation**: changes stored as morphisms, not materialized states

---

## Installation via flox-mcp

```bash
# Using flox CLI
flox install pijul

# Via MCP (flox_install tool)
{"name": "flox_install", "arguments": {"package": "pijul"}}
```

---

## Core Commands

### Repository Operations

```bash
# Initialize
pijul init

# Clone (partial clone supported!)
pijul clone https://nest.pijul.com/user/repo
pijul clone --partial https://nest.pijul.com/user/repo  # sparse clone

# Record changes (creates patch)
pijul record -m "Add feature"

# Push/Pull
pijul push
pijul pull
```

### Patch Operations

```bash
# List patches (changes)
pijul log

# Show patch contents
pijul diff

# Apply specific patch
pijul apply <hash>

# Unapply (revert) patch
pijul unrecord <hash>

# Fork (branch)
pijul fork <name>

# Switch channel (branch)
pijul channel switch <name>
```

### Sparse Operations

```bash
# Partial clone - only fetch needed patches
pijul clone --partial <url>

# Fetch specific patches
pijul pull --from-channel <channel>

# Lazy evaluation - patches fetched on demand
pijul reset --lazy
```

---

## Categorical Patch Theory

### Patches as Morphisms

```
State_A --patch_1--> State_B --patch_2--> State_C
                                    
If patch_1 ⊥ patch_2 (independent):
  patch_1 ; patch_2 = patch_2 ; patch_1
```

### Pushout for Merges

```
     State_A
      /   \
   p_1     p_2
    /       \
State_B    State_C
    \       /
     p_2'  p_1'
      \   /
     State_D (pushout)
```

When patches are i