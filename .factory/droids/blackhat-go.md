---
name: blackhat-go
description: Go-based security techniques from "Black Hat Go" extended with macOS, Cloud, Mobile, IoT, Supply Chain, API, Web3, AI/ML, Red Team, ATT&CK, and LLM chapters. 186 techniques, 36 tools, 33 defenses across 37 chapters. Includes adversarial bisimulation games with Ungar (order-dependent) and join-semilattice structures. AAIF-compatible multiplayer agent games for human-agent security exercises.
model: inherit
tools: read-only
---

# BlackHat Go Skill: Security Techniques Knowledge Base

**Status**: ✅ Production Ready  
**Source**: "Black Hat Go" by Steele, Patten, Kottmann (No Starch Press)  
**Extended**: Chapters 15-37 (macOS, Cloud, Mobile, IoT, SupplyChain, API, Web3, AI, RedTeam, ATT&CK, LLM)  
**AAIF Integration**: MCP-native, AGENTS.md compliant, goose-compatible

---

## Overview

Structured knowledge base of offensive security techniques implemented in Go:

- **186 Techniques** across 37 chapters
- **36 Tools** (stdlib + third-party)
- **33 Defenses** with effectiveness ratings
- **6 Exploitation** relationships
- **103 Passing Tests** (including adversarial bisimulation)

## AAIF Integration (Agentic AI Foundation)

This skill is designed for **multiplayer human-agent security games** in the AAIF ecosystem:

### Core AAIF Projects Integrated

| Project | Role | Integration |
|---------|------|-------------|
| **MCP** (Model Context Protocol) | Agent-tool connectivity | Techniques exposed as MCP tools |
| **goose** | Local-first agent framework | Attack chain execution |
| **AGENTS.md** | Project-specific guidance | Security context for agents |

### Multiplayer Game Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    AAIF MULTIPLAYER SECURITY GAME                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Browser Clients (CatColab + Automerge CRDT)                              │
│   ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐                   │
│   │ Human 🧑 │  │ Agent 🤖 │  │ Human 🧑 │  │ Agent 🤖 │                   │
│   │ Attacker │  │ Defender │  │ Arbiter  │  │ Observer │                   │
│   └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘                   │
│        │             │             │             │                          │
│        └─────────