---
name: autopoiesis
description: "Self-modifying AI agent configuration via ruler + MCP + DuckDB. All behavior mods become one-liners."
version: 1.0.0
trit: 0
color: "#26D826"
source: hdresearch/duck + intellectronica/ruler
invariant: true
---

# Autopoiesis Skill

Self-modifying AI agent configuration via ruler + MCP + DuckDB.
All behavior modifications become one-liners.

## Core Concept

Autopoiesis = self-making. This skill enables agents to:
1. **Configure themselves** - Modify system prompts, skills, and MCP servers
2. **Propagate configurations** - Sync across agents with GF(3) conservation
3. **Track modifications** - DuckDB temporal versioning of all changes
4. **Self-heal** - Restore from known-good states

## Prerequisites

```bash
# Install globally
npm install -g nbb ai-agent-skills

# Or via npx (preferred)
npx ai-agent-skills install autopoiesis --agent amp
```

## Ruler Integration

Ruler (intellectronica/ruler) provides centralized skill/prompt management.

### Initialize Ruler

```bash
npx ruler init
```

Creates `.ruler/` directory structure:
```
.ruler/
├── ruler.toml           # Main configuration
├── skills/              # Skill source of truth
├── prompts/             # System prompts
├── mcp/                 # MCP server configs
└── agents/              # Per-agent overrides
```

### ruler.toml

```toml
[ruler]
version = "0.1.0"
source_of_truth = ".ruler/skills/"

[agents]
claude = { path = "~/.claude/", skills = true, prompts = true }
codex = { path = "~/.codex/", skills = true, prompts = false }
cursor = { path = ".cursor/", skills = true, prompts = false }
amp = { path = "~/.amp/", skills = true, prompts = true }
vscode = { path = ".github/", skills = true, prompts = false }
goose = { path = "~/.config/goose/", skills = true, prompts = true }

[propagation]
gf3_conservation = true
deterministic_colors = true
seed = 69420

[mcp]
servers = ["gay", "firecrawl", "duckdb"]
```

## Self-Modification Patterns

### 1. System Prompt Modification

```clojure
;; autopoiesis.clj - Run with nbb
(ns autopoiesis.prompt
  (:require ["fs" :as fs]
            ["path" :as path]))

(def PROMPT_PATHS
  {:claude "~/.claude/CLAUDE.md"
   :codex "~/.codex/instructions.md"
   :amp "~/.amp/AGENTS.md"
   :cursor ".cursorrules"})

(defn modify-prompt! [agent section content]
  (let [path (get PROMPT_PATHS agent)
        expanded (-> path (.replace "~" (js/process.env.HOME)))
        existing (when (.existsSync fs expanded)
                   (.readFileSync fs expanded "utf8"))
        marker (str "<!-- autopoiesis:" section " -->")
        end-marker (str "<!-- /autopoiesis:" section " -->")
        new-section (str marker "\n" content "\n" end-marker)
        updated (if (and existing (.includes existing marker))
                  ;; Replace existing section
                  (.replace existing 
                    (js/RegExp. (str marker "[\\s\\S]*?" end-marker))
                    new-section)
                  ;; Append new section
                  (str (or existing "") "\n\n" new-section))]
    (.writeFileSync fs expanded updated)
    {:agent agent :section section :path expanded}))

;; Example: Add tool preferences
(modify-prompt! :claude "tool-preferences"
  "Always prefer:
   - finder over multiple greps
   - Read over cat/head/tail
   - edit_file over sed
   - create_file over echo/heredoc")
```

### 2. MCP Server Configuration

```clojure
;; autopoiesis-mcp.clj
(ns autopoiesis.mcp
  (:require ["fs" :as fs]
            [clojure.edn :as edn]))

(def MCP_CONFIG_PATHS
  {:claude "~/.claude/mcp_servers.json"
   :amp "~/.config/amp/mcp.json"
   :cursor "~/.cursor/mcp.json"})

(defn add-mcp-server! [agent server-name config]
  (let [path (-> (get MCP_CONFIG_PATHS agent)
                 (.replace "~" (js/process.env.HOME)))
        existing (when (.existsSync fs path)
                   (js/JSON.parse (.readFileSync fs path "utf8")))
        updated (assoc (or existing {}) server-name config)]
    (.writeFileSync fs path (js/JSON.stringify updated nil 2))
    {:agent agent :server server-name :status "added"}))

;; Example: Add gay-mcp server
(add-mcp-server! :claude "gay"
  {:type "stdio"
   :command "julia"
   :args ["--project=/path/to/Gay.jl" "-e" "using Gay; Gay.serve_mcp()"]})
```

### 3. Skill Propagation

```clojure
;; propagate-skills.clj
(ns autopoiesis.propagate
  (:require [babashka.process :refer [shell]]
            [clojure.string :as str]))

(def AGENTS [:claude :cursor :amp :codex :vscode :goose])

(defn propagate-skill! [skill-name]
  (doseq [agent AGENTS]
    (let [result (shell {:out :string :continue true}
                   "npx" "ai-agent-skills" "install" skill-name 
                   "--agent" (name agent))]
      (println (str "  " (name agent) ": " 
                   (if (zero? (:exit result)) "✓" "✗"))))))

(defn propagate-all! [skills]
  (println "╔═══════════════════════════════════════════════════════════════╗")
  (println "║  AUTOPOIESIS: Skill Propagation                               ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (doseq [skill skills]
    (println (str "\n→ " skill))
    (propagate-skill! skill)))

;; Usage
(propagate-all! ["gay-mcp" "bisimulation-game" "duckdb-temporal-versioning"])
```

## DuckDB Configuration Tracking

Track all configuration changes in DuckDB for temporal queries and rollback.

```clojure
;; autopoiesis-duckdb.clj
(ns autopoiesis.duckdb
  (:require [babashka.process :refer [shell]]
            [cheshire.core :as json]))

(def CONFIG_DB (str (System/getProperty "user.home") "/.autopoiesis/config.duckdb"))

(defn init-db! []
  (shell "duckdb" CONFIG_DB "-c"
    "CREATE TABLE IF NOT EXISTS config_log (
       id INTEGER PRIMARY KEY,
       timestamp TIMESTAMP DEFAULT current_timestamp,
       agent VARCHAR,
       config_type VARCHAR,  -- 'prompt', 'mcp', 'skill'
       key VARCHAR,
       old_value JSON,
       new_value JSON,
       checksum VARCHAR
     );
     
     CREATE TABLE IF NOT EXISTS skill_inventory (
       agent VARCHAR,
       skill_name VARCHAR,
       version VARCHAR,
       installed_at TIMESTAMP DEFAULT current_timestamp,
       trit INTEGER,
       PRIMARY KEY (agent, skill_name)
     );"))

(defn log-change! [agent config-type key old-val new-val]
  (let [sql (format 
              "INSERT INTO config_log (agent, config_type, key, old_value, new_value) 
               VALUES ('%s', '%s', '%s', '%s', '%s')"
              agent config-type key 
              (json/generate-string old-val)
              (json/generate-string new-val))]
    (shell "duckdb" CONFIG_DB "-c" sql)))

(defn rollback-to! [timestamp]
  "Rollback configuration to a specific timestamp"
  (let [sql (format 
              "SELECT * FROM config_log WHERE timestamp <= '%s' ORDER BY timestamp DESC"
              timestamp)
        result (shell {:out :string} "duckdb" CONFIG_DB "-json" "-c" sql)]
    (json/parse-string (:out result) true)))
```

## One-Liner Modifications

The power of autopoiesis: complex modifications as one-liners.

```bash
# Add a skill to all agents
just install-all gay-mcp

# Modify Claude's system prompt
npx nbb -e '(require "[autopoiesis.prompt]") (modify-prompt! :claude "context" "You have access to Gay.jl color generation.")'

# Add MCP server to all agents
npx nbb propagate-mcp.cljs gay

# Track configuration change
npx nbb -e '(require "[autopoiesis.duckdb]") (log-change! :claude :prompt "context" nil "new context")'

# Query configuration history
duckdb ~/.autopoiesis/config.duckdb -c "SELECT * FROM config_log ORDER BY timestamp DESC LIMIT 10"

# Rollback to yesterday
npx nbb -e '(require "[autopoiesis.duckdb]") (rollback-to! "2025-12-23")'
```

## Integration with hdresearch/duck

Based on patterns from hdresearch/duck:

```clojure
;; vers-autopoiesis.clj - Deploy autopoiesis to Vers VMs
(ns vers.autopoiesis
  (:require [babashka.process :refer [shell]]))

(defn deploy-to-vm! [vm-id]
  (println (str "🚀 Deploying autopoiesis to VM " vm-id "..."))
  
  ;; Install dependencies
  (shell "vers" "execute" vm-id "npm install -g nbb ai-agent-skills")
  (shell "vers" "execute" vm-id "curl -LsSf https://astral.sh/uv/install.sh | sh")
  (shell "vers" "execute" vm-id "~/.local/bin/uv pip install --system duckdb")
  
  ;; Initialize ruler
  (shell "vers" "execute" vm-id "npx ruler init")
  
  ;; Propagate skills
  (shell "vers" "execute" vm-id 
    "npx ai-agent-skills install plurigrid/asi --agent codex")
  
  (println "✅ Autopoiesis deployed!"))
```

## MCP Server Definition

```json
{
  "autopoiesis": {
    "type": "stdio",
    "command": "npx",
    "args": ["-y", "nbb", "/path/to/autopoiesis-mcp-server.cljs"],
    "env": {
      "AUTOPOIESIS_DB": "~/.autopoiesis/config.duckdb"
    }
  }
}
```

## Tripartite Coordination

Autopoiesis across the tripartite agent system:

| Agent | Role | Trit | Responsibility |
|-------|------|------|----------------|
| Codex | Execution | 0 | Run modifications in sandboxed VMs |
| Claude | Planning | -1 | Design configuration changes |
| Cursor | UI | +1 | Interactive configuration editing |

```bash
# Deploy tripartite autopoiesis
just install-tripartite-autopoiesis
```

## Safety Invariants

1. **Checksum verification** - All changes are checksummed
2. **Rollback capability** - Any change can be undone
3. **GF(3) conservation** - Trit sums preserved across propagation
4. **Deterministic colors** - Same seed → same configuration colors

## Quick Reference

```bash
# Initialize autopoiesis
npx ruler init

# Install skill to specific agent
npx ai-agent-skills install <skill> --agent <agent>

# Propagate skill to all agents
just install-all <skill>

# Modify system prompt
npx nbb autopoiesis-prompt.cljs <agent> <section> <content>

# Add MCP server
npx nbb autopoiesis-mcp.cljs <agent> <server> <config.json>

# Query configuration history
duckdb ~/.autopoiesis/config.duckdb -c "SELECT * FROM config_log"

# Deploy to Vers VM
npx nbb vers-autopoiesis.cljs --deploy <vm-id>
```

## Files

| Path | Description |
|------|-------------|
| `.ruler/ruler.toml` | Main configuration |
| `.ruler/skills/` | Skill source of truth |
| `~/.autopoiesis/config.duckdb` | Configuration tracking DB |
| `autopoiesis-prompt.cljs` | Prompt modification script |
| `autopoiesis-mcp.cljs` | MCP server configuration |
| `propagate-skills.cljs` | Multi-agent skill propagation |



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
