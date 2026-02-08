---
name: workspace-unified
description: Unified Google Workspace management via WorkspaceACSet. Transforms operations into GF(3)-typed Interactions across Gmail, Drive, Calendar, Tasks, Docs with cross-skill morphisms and MCP↔API equivalence. Use for multi-service workflows or applying ACSet principles to workspace automation.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Workspace Unified Skill

Transform Google Workspace into an ACSet-structured system with GF(3) conservation and cross-skill morphisms.

**Trit**: 0 (ERGODIC - coordinator)  
**Principle**: Workflow Completion = Condensed Equilibrium State  
**Implementation**: WorkspaceACSet + PathInvariance + MCPAPIBridge

## Overview

Workspace Unified applies categorical database principles to workspace:

1. **Transform** - Operations → GF(3)-typed Interactions
2. **Route** - Interactions → Service-specific ACSet objects
3. **Compose** - Cross-skill morphisms with path commutativity
4. **Verify** - MCP↔API equivalence and Narya proofs

## WorkspaceACSet Schema

```
┌─────────────────────────────────────────────────────────────────────────────────────────┐
│                              WorkspaceACSet Schema                                       │
├─────────────────────────────────────────────────────────────────────────────────────────┤
│                                                                                          │
│  Interaction ───────────┬──────▶ Thread ◀───────────────── DriveFile                    │
│  ├─ verb: String        │        ├─ thread_id: String       ├─ file_id: String          │
│  ├─ timebin: Int        │        ├─ needs_action: Bool      ├─ mime_type: String        │
│  ├─ trit: Trit          │        ├─ last_action_bin: Int    └─ saturated: Bool          │
│  ├─ service: Service    │        └─ saturated: Bool                                      │
│  └─ person ─────────────┼──▶                                                             │
│                         │                                                                │
│  CalendarEvent ◀────────┼──────── TaskList ◀────────────── Task                         │
│  ├─ event_id: String    │         ├─ list_id: String        ├─ task_id: String          │
│  ├─ summary: String     │         └─ title: String          ├─ title: String            │
│  ├─ start: DateTime     │                  