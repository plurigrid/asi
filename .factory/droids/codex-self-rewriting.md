---
name: codex-self-rewriting
description: Lisp machine self-modification patterns via MCP Tasks and Narya bridge
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# codex-self-rewriting - Lisp Machine Self-Modification via MCP Tasks

## Overview

Enables Codex (OpenAI's CLI agent) to achieve Lisp-machine-like self-rewriting capabilities through MCP Tasks integration. Uses Narya observational bridge types for structure-aware modifications.

## Core Concept: Cognitive Continuity via Babashka Transients

```clojure
;; gay.bb transient state
(def ^:dynamic *cognitive-state*
  {:seed 0x42D
   :fingerprint (atom 0)
   :tap-state :VERIFY
   :color-history []})

;; Fork on modification
(defn fork-state! [intervention]
  (let [new-seed (bit-xor (:seed *cognitive-state*)
                          (hash intervention))]
    (assoc *cognitive-state* :seed new-seed)))
```

## MCP Tasks Integration

Based on [MCP Tasks Specification](https://modelcontextprotocol.io/specification/draft/basic/utilities/tasks):

### Task States for Self-Rewriting

| Status | TAP State | Meaning |
|--------|-----------|---------|
| `working` | LIVE (+1) | Modification in progress |
| `input_required` | VERIFY (0) | Needs human approval |
| `completed` | BACKFILL (-1) | Modification archived |
| `failed` | BACKFILL (-1) | Rollback applied |
| `cancelled` | VERIFY (0) | Intervention stopped |

### Capabilities Declaration

```json
{
  "capabilities": {
    "tasks": {
      "list": {},
      "cancel": {},
      "requests": {
        "tools": {
          "call": {}
        }
      }
    }
  }
}
```

## Narya Observational Bridge Types

Following Topos Institute structure-aware version control:

1. **Diffs as logical relations** - Computed inductively from skill type
2. **Conflicts as 2D cubical** - Skill modifications form commuting squares
3. **Type changes as spans** - Skill version correspondences

### Bridge Colors

```elisp
;; From narya_observational_bridge.el
(defconst tap/BACKFILL -1)  ; Blue  - Historical
(defconst tap/VERIFY 0)     ; Green - Verification
(defconst tap/LIVE +1)      ; Red   - Active modification
```

## Self-Rewriting Protocol

```bash
# 1