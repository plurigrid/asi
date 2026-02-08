---
name: keychain-secure
description: macOS Keychain credential management with GF(3) balanced operations
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Keychain Secure Skill: GF(3) Balanced Credential Management

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - validator/security)
**Color**: #2626D8 (Blue)
**Principle**: Store(+1) + Retrieve(0) + Validate(-1) = 0
**Frame**: Never env vars, always Keychain

---

## Overview

**Keychain Secure** provides secure credential storage on macOS with GF(3) conservation. Every credential lifecycle is balanced:

```
Create (+1) → Transport (0) → Consume/Verify (-1) = 0 ✓
```

## GF(3) Triads

```
keychain-secure (-1) ⊗ mdm-cobordism (0) ⊗ gay-mcp (+1) = 0 ✓  [Credential Chain]
keychain-secure (-1) ⊗ unworld (0) ⊗ oapply-colimit (+1) = 0 ✓  [Derivation]
keychain-secure (-1) ⊗ acsets (0) ⊗ koopman-generator (+1) = 0 ✓  [Pattern]
```

## Why Not Environment Variables?

| Storage | Security | Problem |
|---------|----------|---------|
| `export API_KEY=...` | ❌ None | Visible in `ps`, logs, shell history |
| `.env` file | ❌ Minimal | Readable, often committed to git |
| Keychain | ✅ Encrypted | Hardware-backed, ACL-protected |

**Rule**: Secrets belong in Keychain, never in environment.

## Commands

### Store Credential (+1 Generator)

```bash
# Interactive (prompts for password)
security add-generic-password \
    -s "service-name" \
    -a "$USER" \
    -w

# Non-interactive (⚠️ visible in process list briefly)
security add-generic-password \
    -s "service-name" \
    -a "$USER" \
    -w "secret-value" \
    -U  # Update if exists
```

### Retrieve Credential (0 Coordinator)

```bash
# Get password value
security find-generic-password \
    -s "service-name" \
    -a "$USER" \
    -w

# Use in command substitution
export API_KEY=$(security find-generic-password -s "openai" -a "$USER" -w)
```

### Delete Credential (-1 Validator)

```bash
security delete-generic-password \
    -s "service-name" \
    -a "$USER"
```

### Verify Credential (-1 Validator)

```bash
# Check if credential exists and is retrievable
security find-generic-password -s "service-name" -a "$USER" -w