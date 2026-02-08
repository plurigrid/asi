---
name: crdt
description: crdt skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CRDT Skill - Conflict-free Replicated Data Types

**Status**: ✅ Production Ready
**Framework**: Jules Hedges' Compositional Game Theory
**Language**: Ruby (HedgesOpenGames module)
**Trit**: ±1 (covariant/contravariant)
**Integration**: Amp, Codex, Music-Topos CRDT

## bmorphism Contributions

> *"all is bidirectional"*
> — [@bmorphism](https://gist.github.com/bmorphism/ead83aec97dab7f581d49ddcb34a46d4), Play/Coplay gist

> *"Automerge is a local-first sync engine for multiplayer apps that works offline, prevents conflicts, and runs fast."*
> — [Automerge](https://automerge.org/)

**Plurigrid Connection**: CRDTs embody the principle of **autopoietic ergodicity** — self-sustaining distributed systems that explore all accessible states and converge automatically. This aligns with bmorphism's vision of:
- **Local-first** computing (offline-capable, no single point of failure)
- **Bidirectional sync** (Play/Coplay structure for state transfer)
- **Conflict-free** composition (open games with guaranteed Nash equilibria)

**Key References**:
- [Automerge](https://github.com/automerge/automerge) - JSON-like CRDTs for offline-first apps
- [Yjs](https://yjs.dev/) - High-performance CRDT framework
- [Compositional Game Theory](https://arxiv.org/abs/1603.04641) - Open games foundation for Play/Coplay

Related to bmorphism's work on:
- [plurigrid/act](https://github.com/plurigrid/act) - cognitive category theory with eventual consistency
- Parametrised optics for bidirectional state transfer

## Overview

The CRDT Skill provides conflict-free replicated data types with bidirectional lens optics for compositional game theory. It implements core CRDT types with full merge semantics and property verification.

## Features

### Core CRDT Types

1. **LWW Register** (Last-Write-Wins)
   - Timestamp-based value ordering
   - Simple conflict resolution
   - Use case: Simple mutable state

2. **G-Counter** (Grow-only Counter)
   - Monotonically increasing counts
   - Distributed increm