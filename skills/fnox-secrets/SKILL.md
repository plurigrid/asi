---
name: fnox-secrets
description: fnox Secrets Management Skill - DIRECT PIPE ONLY
version: 2.0.0
---

# fnox Secrets Management Skill

```yaml
name: fnox-secrets
description: Secure secrets management - SECRETS MUST NEVER BE EXPOSED IN CONTEXT
version: 2.0.0
trit: -1  # Validator/constrainer role in GF(3) triadic system
```

## CRITICAL SECURITY RULE

**SECRETS MUST NEVER APPEAR IN CLAUDE'S CONTEXT OR OUTPUT.**

The ONLY permitted pattern is direct piping into environment variables:

```bash
# CORRECT - secret never visible
SECRET_NAME=$(fnox get SECRET_NAME --age-key-file ~/.age/key.txt) command_that_uses_it

# FORBIDDEN - exposes secret to context
fnox get SECRET_NAME --age-key-file ~/.age/key.txt  # NEVER DO THIS
```

## Permitted Operations

### 1. Direct Pipe to Environment Variable

```bash
# Pipe secret directly into env var for a command
MORPH_API_KEY=$(fnox get MORPH_API_KEY --age-key-file ~/.age/key.txt) uv run python script.py
APTOS_KEY=$(fnox get APTOS_ALICE_KEY --age-key-file ~/.age/key.txt) aptos move run ...
```

### 2. List Secret Names (NOT values)

```bash
fnox list  # Shows names only, never values
```

### 3. Check Secret Exists

```bash
fnox list | grep -q SECRET_NAME && echo "exists"
```

### 4. Set a Secret (user provides value, not Claude)

```bash
fnox set SECRET_NAME --provider myage  # User enters value interactively
```

## FORBIDDEN Operations

- `fnox get SECRET` without piping to a command
- Storing secret output in a variable that gets logged
- Printing, echoing, or displaying secret values
- Including secrets in error messages or debug output
- Any operation that would expose the secret in Claude's context

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  FNOX SECURE ARCHITECTURE                                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ~/.age/key.txt ────────────────┐                                          │
│                                 │                                           │
│                                 ▼                                           │
│  fnox get ──▶ DECRYPTS ──▶ $(...) ──▶ ENV VAR ──▶ SUBPROCESS               │
│                    │                                                        │
│                    └──▶ NEVER TO STDOUT/CONTEXT                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Usage Examples

### Morph Cloud

```bash
MORPH_API_KEY=$(fnox get MORPH_API_KEY --age-key-file ~/.age/key.txt) uv run python -c "
from morphcloud.api import MorphCloudClient
client = MorphCloudClient()
# ... use client
"
```

### Aptos

```bash
APTOS_PRIVATE_KEY=$(fnox get APTOS_ALICE_KEY --age-key-file ~/.age/key.txt) aptos move run \
  --function-id 0x1::coin::transfer \
  --args address:0x... u64:1000000
```

### Multiple Secrets

```bash
# Chain multiple secrets in one command
MORPH_API_KEY=$(fnox get MORPH_API_KEY --age-key-file ~/.age/key.txt) \
DUNE_API_KEY=$(fnox get DUNE_API_KEY --age-key-file ~/.age/key.txt) \
  python my_script.py
```

## Available Secrets (names only)

Query with: `fnox list`

Categories:
- `APTOS_*` - Blockchain keys
- `MORPH_API_KEY` - Morph Cloud
- `DUNE_API_KEY` - Dune Analytics
- `AMP_API_KEY` - AMP
- `BEEPER_ACCESS_TOKEN` - Beeper

## GF(3) Trit Assignment

```
fnox-secrets: -1 (validator/constrainer)
```

Participates in triads:
```
fnox-secrets (-1) ⊗ world-runtime (0) ⊗ gay-mcp (+1) = 0 ✓
```

## 1Password Provider Bridge

fnox natively supports 1Password as a provider backend. Secrets stored in 1Password can be accessed through the same `fnox get` interface.

### Setup

```bash
# Add 1Password as a provider
fnox provider add op 1password

# Configure vault in fnox.toml
```

```toml
# fnox.toml
[providers.op]
type = "1password"
vault = "Employee"
```

### Defining 1Password-backed Secrets

Use `op://` secret references as the value:

```toml
[secrets.MY_API_KEY]
provider = "op"
value = "op://Employee/MyAPIKey/password"
```

### Usage (same interface as age secrets)

```bash
# CORRECT - direct pipe, secret never in context
eval $(op signin)
MY_API_KEY=$(fnox get MY_API_KEY --age-key-file ~/.age/key.txt) ./my-command

# Works identically to age-backed secrets
MORPH_API_KEY=$(fnox get MORPH_API_KEY --age-key-file ~/.age/key.txt) \
MY_API_KEY=$(fnox get MY_API_KEY --age-key-file ~/.age/key.txt) \
  python my_script.py
```

### Mixed Provider Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  fnox get SECRET_NAME                                        │
│       │                                                      │
│       ├── provider = "myage" ──▶ age decrypt (local/offline) │
│       │                                                      │
│       └── provider = "op" ──▶ op read op://... (1Password)   │
│                                  │                           │
│                                  └── requires eval $(op signin) │
│                                                              │
│  Both paths ──▶ $(...) ──▶ ENV VAR ──▶ SUBPROCESS            │
│                     └──▶ NEVER TO STDOUT/CONTEXT             │
└─────────────────────────────────────────────────────────────┘
```

### When to Use Which Provider

| Provider | Use Case |
|----------|----------|
| `myage` (age) | Offline access, CI/CD, air-gapped systems |
| `op` (1Password) | Team-shared secrets, credential rotation, audit trail |
