---
name: docs-acset
description: Google Docs/Sheets management via ACSet condensation. Transforms documents into GF(3)-typed Interactions, tracks comments/cells, detects saturation when all comments resolved. Use for document workflows, spreadsheet automation, or applying ANIMA principles to Workspace documents.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Docs ACSet Skill

Transform Google Docs/Sheets into an ACSet-condensed system with GF(3) conservation.

**Trit**: 0 (ERGODIC - coordinator)  
**Principle**: Published Document = Condensed State  
**Implementation**: DocsACSet + CommentTracker + CellSaturation

## Overview

Docs ACSet applies category-theoretic structure to documents:

1. **Transform** - Documents/Sheets → GF(3)-typed Interactions
2. **Track** - Comments/Cells → Saturation state
3. **Detect** - All resolved → ANIMA condensed state
4. **Verify** - Narya proofs for consistency

## DocsACSet Schema

```
┌────────────────────────────────────────────────────────────────────┐
│                      DocsACSet Schema                              │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  Document ────────┬────▶ Section                                   │
│  ├─ doc_id: String│      ├─ heading: String                        │
│  ├─ title: String │      ├─ level: Int                             │
│  └─ published: Bool      └─ content_hash: String                   │
│                   │                                                │
│  Comment ─────────┼────▶ Thread (doc)                              │
│  ├─ content: String      ├─ resolved: Bool                         │
│  ├─ author: String       └─ reply_count: Int                       │
│  └─ trit: Trit    │                                                │
│                   │                                                │
│  Spreadsheet ─────┼────▶ Sheet                                     │
│  ├─ ss_id: String │      ├─ name: String                           │
│  └─ locale: String       └─ row_count: Int                         │
│                   │                                                │
│  Cell ────────────┴────▶ Range                                     │
│  ├─ value: String        ├─ a1_notation: String                    │
│  ├─