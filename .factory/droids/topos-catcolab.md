---
name: topos-catcolab
description: Topos Institute's CatColab for collaborative category theory - community model building, double theories, stock and flow epidemiology, and real-time collaborative diagramming via Automerge CRDT.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CatColab: Collaborative Category Theory

**Trit**: 0 (ERGODIC - coordinator)
**Color**: Blue (#4A90D9)

## Overview

CatColab is Topos Institute's platform for **formal, interoperable, conceptual modeling** using applied category theory. It enables:

- **Community Model Building**: Groups collaboratively construct categorical models
- **Double Categories**: Theories as double categorical structures (DOTS)
- **Stock & Flow**: Epidemiological modeling with categorical semantics
- **Real-time Collaboration**: Automerge CRDT for conflict-free multi-user editing

## Core Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    CatColab Platform                     │
├─────────────────────────────────────────────────────────┤
│  Frontend (SolidJS)                                      │
│  ├── ModelNotebookEditor   → Object/Morphism declarations│
│  ├── DiagramNotebookEditor → Visual diagram authoring    │
│  └── AnalysisNotebookEditor → ODE simulation, export     │
├─────────────────────────────────────────────────────────┤
│  Automerge CRDT Sync Layer                               │
│  ├── DocHandle (document state)                          │
│  ├── WebSocket sync to server                            │
│  └── Reconcile → SolidJS reactivity                      │
├─────────────────────────────────────────────────────────┤
│  catlog (Rust Engine via WASM)                           │
│  ├── Double theories (DiscreteDblTheory, ModalDblTheory) │
│  ├── Model elaboration & validation                      │
│  └── ODE integration for stock-flow                      │
├─────────────────────────────────────────────────────────┤
│  Backend (Axum + PostgreSQL)                             │
│  └── Document persistence, auth, Julia interop           │
└─────────────────────────────────────────────────────────┘
```

## Key Features

### 1. Community Model Building Events

CatColab supports participatory modeling workshops:

```typescript
// 