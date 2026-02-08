---
name: captp
description: "CapTP: Capability Transfer Protocol"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CapTP: Capability Transfer Protocol

**Trit**: 0 (ERGODIC - transports capabilities without amplification)
**Color**: #46F27F (Coordinator stream)
**Source**: Spritely Goblins (codeberg.org/spritely/goblins)

---

## Overview

CapTP (Capability Transfer Protocol) enables distributed object programming with capability security. Objects can live anywhere on the network; CapTP abstracts location so programmers focus on object interaction, not protocol architecture.

**Core principle**: Capabilities are unforgeable references. You can only invoke what you've been given.

---

## Key Concepts

### Vats (Actor Containers)

```scheme
;; Guile Goblins
(define vat (spawn-vat))
(define greeter (vat-spawn vat ^greeter))
```

| Concept | Description | Trit Mapping |
|---------|-------------|--------------|
| **Vat** | Transactional actor container | 0 (ergodic boundary) |
| **Actor** | Encapsulated object with behavior | +1 (generative) |
| **Capability** | Unforgeable reference | -1 (constraining) |

### Promise Pipelining

```scheme
;; Don't wait for result - pipeline through promises
(<- (<- alice 'get-friend) 'greet "Hello")
```

Reduces round-trips: send message to promise, network resolves.

### Sturdy vs Live References

| Reference | Persistence | Use Case |
|-----------|-------------|----------|
| **Live** | Session only | Active communication |
| **Sturdy** | Survives restart | Reconnection, storage |

---

## CapTP Message Types

```
op:deliver-only  → Fire-and-forget message
op:deliver       → Message expecting response
op:pick          → Select from multiple promises
op:abort         → Cancel pending operation
op:listen        → Subscribe to updates
op:gc            → Garbage collection hint
```

---

## GF(3) Triads

```
# Core CapTP Bundle
keychain-secure (-1) ⊗ captp (0) ⊗ gay-mcp (+1) = 0 ✓  [Secure Transport]
shadow-goblin (-1) ⊗ captp (0) ⊗ agent-o-rama (+1) = 0 ✓  [Distributed Actors]
polyglot-spi (-1) ⊗ captp (0) ⊗ pulse-mcp-stream (+1) = 0 ✓  [Cross-Lang