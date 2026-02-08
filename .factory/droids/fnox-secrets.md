---
name: fnox-secrets
description: fnox Secrets Management Skill - DIRECT PIPE ONLY
model: inherit
tools: read-only
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
│             