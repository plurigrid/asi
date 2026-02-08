---
name: mdm-cobordism
description: macOS MDM with auth manifolds as cobordisms for credential derivation
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

# MDM Cobordism Skill: Auth Manifolds as State Transitions

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - transport/derivation)
**Color**: #26D826 (Green)
**Principle**: Auth is cobordism W: ∂₀ → ∂₁, not event sequence
**Frame**: No demos, only derivation

---

## Overview

**MDM Cobordism** models authentication and device management as cobordisms — manifolds with boundaries representing auth state transitions. Following the **unworld** philosophy:

- Credentials don't "exist" — they **derive**
- There is no "authentication event" — only state derivation
- Keys don't "expire" — their chain position becomes unreachable

## GF(3) Triads

Forms valid triads with MINUS (-1) and PLUS (+1) skills:

```
sheaf-cohomology (-1) ⊗ mdm-cobordism (0) ⊗ gay-mcp (+1) = 0 ✓  [Credential Derivation]
temporal-coalgebra (-1) ⊗ mdm-cobordism (0) ⊗ oapply-colimit (+1) = 0 ✓  [State Observation]
three-match (-1) ⊗ mdm-cobordism (0) ⊗ koopman-generator (+1) = 0 ✓  [Pattern Learning]
```

## Auth Cobordisms

| Cobordism | Source → Target | Trit | Role |
|-----------|-----------------|------|------|
| W₁ generate_key | Unauth → HasKey | +1 | Generator |
| W₂ request_scep | HasKey → HasCert | 0 | Coordinator |
| W₃ validate_cert | HasCert → HasToken | -1 | Validator |
| W₄ check_in_mdm | HasToken → Enrolled | +1 | Generator |
| W₅ verify_enroll | Enrolled → Enrolled | -1 | Validator |

**GF(3) Conservation**: `+1 + 0 + (-1) + (+1) + (-1) = 0 ✓`

## Boundary Types

```python
# Auth manifold boundaries
Unauthenticated  # ∂₀: No identity
HasKey           # Device has private key
HasCertificate   # Device has CA-signed cert
HasToken         # Device has session token
Enrolled         # Device enrolled in MDM
Supervised       # Device under full management
```

## Keychain Integration

macOS Keychain operations with GF(3) tracking:

```python
# Store (+1) → Retrieve (0) → Validate (-1) = 0 ✓
Keychain.store_then_verify(service, account, secret)
```

| Operation | Trit | Description |
|---