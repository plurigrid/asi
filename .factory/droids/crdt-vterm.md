---
name: crdt-vterm
description: Collaborative terminal session sharing using CRDT-style s-expressions
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CRDT-VTerm - Collaborative Terminal Sharing

Collaborative terminal session sharing using CRDT-style s-expressions with GF(3) trifurcated conflict resolution.

## Components

### Emacs Bridge
- **File**: `crdt-vterm-bridge.el`
- **Purpose**: Connect vterm.el to crdt.el via shadow buffers

### Babashka Recorder
- **File**: `vterm_crdt_recorder.bb`
- **Purpose**: Record/replay terminal sessions as CRDT sexps

### P2P Sharing
- **File**: `vterm_localsend_share.bb`  
- **Purpose**: Live terminal sharing via localsend multicast

## Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│                    CRDT-VTerm System                             │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────┐     remote-insert     ┌───────────────┐             │
│  │ vterm   │ ───────────────────▶  │ shadow buffer │             │
│  │  PTY    │      (GF3 trit)       │  (crdt.el)    │             │
│  └────┬────┘                       └───────┬───────┘             │
│       │                                    │                     │
│       │ script(1)                          │ sexp file           │
│       ▼                                    ▼                     │
│  ┌─────────┐                       ┌───────────────┐             │
│  │ raw log │                       │ .sexp log     │             │
│  └────┬────┘                       └───────┬───────┘             │
│       │                                    │                     │
│       │ vterm_crdt_recorder.bb             │ localsend UDP       │
│       ▼                                    ▼                     │
│  ┌─────────────────────────────────────────────────┐             │
│  │              P2P Peer Network                   │             │
│  │  ┌───────┐   ┌───────┐   ┌───────┐              │             │
│  │  │ MINUS │   │ERGODIC│   │ PLUS  │  ← GF(3)     │             