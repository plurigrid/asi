---
name: codex-ocapn-correspondence
description: >-
  Maps the 18 OCapN/CapTP/E-rights patterns reinvented piecemeal across codex-rs
  to their canonical Spritely/Goblins equivalents and the hermes-* bridge skills
  that formalize each correspondence. Use when auditing capability architecture
  in codex-rs, planning a Hoot/Goblins port, or reasoning about which E-rights
  primitive a codex-rs module implicitly implements.
version: 1.0.0
trit: 0
---

# Codex-rs ↔ OCapN Correspondence Map

codex-rs reconstructs nearly the complete OCapN/CapTP/E-rights architecture
piecemeal in Rust. This skill documents the 18-pattern correspondence and
organizes them into six families.

## Six Families

### 1. Core E/CapTP

| # | Pattern | codex-rs Location | OCapN Canonical | hermes-* Bridge |
|---|---------|-------------------|-----------------|-----------------|
| 1 | Swiss Numbers | `windows-sandbox-rs/src/cap.rs` — random session IDs | Unguessable designators for capability addressing | `hermes-cred-as-sturdy` |
| 2 | Eventual-Send | `codex-rs/core` — async message dispatch between threads | `E.send()` / promise pipelining | `hermes-goblins-bridge` |
| 3 | Promise Pipelining (implicit) | `exec/mod.rs` — chained async operations on pending results | Pipelining messages to unresolved promises | `hermes-goblins-bridge` |
| 4 | Near/Far Transparency | `codex-rs/core` — same API for local exec vs sandbox calls | Near refs (same vat) vs far refs (cross-vat) behave identically | `hermes-net-as-cap` |
| 5 | Sturdy References | `core/thread_fork_resume` — resumable thread state persisted to disk | Long-lived, serializable capability references | `hermes-cred-as-sturdy` |

### 2. Rights Amplification

| # | Pattern | codex-rs Location | OCapN Canonical | hermes-* Bridge |
|---|---------|-------------------|-----------------|-----------------|
| 6 | Capability Attenuation | `codex-rs/exec/src/permissions.rs` — `SandboxPolicy` allow/deny lists | Wrapping a cap to restrict its authority | `hermes-tool-as-cap` |
| 7 | Facets & Composition | `protocol/` — tool registration with scoped capabilities | Multiple facets of a single object, each with different authority | `hermes-mcp-as-sealed` |
| 8 | Default-Deny / POLA | `exec/` — sandbox starts with zero capabilities, explicitly grants | Principle of Least Authority as system default | `hermes-fs-as-cap` |

### 3. Lifecycle & Distributed GC

| # | Pattern | codex-rs Location | OCapN Canonical | hermes-* Bridge |
|---|---------|-------------------|-----------------|-----------------|
| 9 | Vat Quiescence | Ephemeral sandbox threads spin down after task completion | Vat pausing / checkpointing | `hermes-session-as-snapshot` |
| 10 | Hierarchical Cancellation | `core/` — parent task cancellation propagates to children | Vat hierarchy with cascading revocation | `hermes-cron-as-dataspace` |
| 11 | Time-Limited Caps | `exec/` — sandbox timeout enforcement | Capabilities with expiry / TTL | `hermes-approval-as-revocable` |
| 12 | Revocation | `exec/` — sandbox teardown revokes all granted caps | Caretaker pattern / revocable forwarders | `hermes-approval-as-revocable` |

### 4. Confinement

| # | Pattern | codex-rs Location | OCapN Canonical | hermes-* Bridge |
|---|---------|-------------------|-----------------|-----------------|
| 13 | Confined Vats | Ephemeral threads as isolated execution contexts | Confined vats with no ambient authority | `hermes-mem-as-dataspace` |
| 14 | Membrane Proxy | `app-server/` — API gateway mediating between user and sandbox | Membrane wrapping all refs crossing a boundary | `hermes-ctx-engine-shim` |
| 15 | Sealed Traits | `protocol/` — type-sealed message envelopes | Sealer/unsealer pairs for type-safe encapsulation | `hermes-mcp-as-sealed` |

### 5. Cryptographic

| # | Pattern | codex-rs Location | OCapN Canonical | hermes-* Bridge |
|---|---------|-------------------|-----------------|-----------------|
| 16 | Sealer/Unsealer | `crypto_box`-style patterns in session auth | Rights amplification via matched seal/unseal pairs | `hermes-mcp-as-sealed` |
| 17 | Opaque Cursors | Session IDs as opaque tokens | Unguessable capability designators | `hermes-cred-as-sturdy` |
| 18 | Swiss-Number SIDs | `cap.rs` — random 128-bit session identifiers | Swiss number addressing | `hermes-cred-as-sturdy` |

### 6. Operational

| Pattern | codex-rs Location | OCapN Canonical | hermes-* Bridge |
|---------|-------------------|-----------------|-----------------|
| Provenance (Horton) | Git-based audit trail in codex-rs sessions | Horton "who said that?" provenance | `hermes-acp-over-captp` |
| Replay | `session-as-snapshot` — deterministic replay from log | Event sourcing / vat replay | `hermes-session-as-snapshot` |
| Backpressure | `exec/` — bounded concurrent tool calls | Mailbox capacity / flow control | `hermes-cron-as-dataspace` |
| Mailbox Ordering | Sequential message processing per sandbox thread | Vat turn-based execution / E-order | `hermes-goblins-bridge` |
| Resource Budgets | `exec/` — timeout + output size limits | Resource-bounded capability exercise | `hermes-tool-as-cap` |

## Port Thesis

A Hoot/Spritely port would collapse all 18 patterns into a single coherent
system because Goblins provides these primitives as first-class abstractions:

- **Swiss numbers** → built-in to CapTP addressing
- **Near/far** → Goblins `spawn` vs `<-` automatically
- **Attenuation** → `define-facet` with restricted methods
- **Confinement** → vat isolation is the default
- **Sealer/unsealer** → `make-sealer-unsealer` primitive
- **Sturdy refs** → `sturdy-ref` with Swiss-number + location hints

The hermes-* bridge skills are the explicit formalization layer: each one
maps exactly one codex-rs reinvention to its Goblins/OCapN canonical form,
enabling incremental migration rather than a big-bang rewrite.

## Related Skills

- `hermes-goblins-bridge` — master bridge skill
- `hermes-acp-over-captp` — ACP↔CapTP protocol mapping
- `hermes-*` family (12 skills) — individual pattern bridges
- `goblins` — Spritely Goblins distributed actor system
- `captp` — CapTP wire protocol
- `guile-goblins-hoot` — Goblins + Hoot WebAssembly compiler
