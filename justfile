# AI Agent Skills - justfile
# Cross-agent skill management for Claude, Cursor, Amp, VS Code, Goose, Codex, Letta
# Autopoiesis: Self-modifying configuration via ruler + MCP + DuckDB + nbb

# Default recipe
default:
    @just --list

# ═══════════════════════════════════════════════════════════════════════════════
# AI-AGENT-SKILLS CLI
# ═══════════════════════════════════════════════════════════════════════════════

# Show ai-agent-skills help
skills-help:
    npx ai-agent-skills help

# Interactive skill browser (TUI)
browse:
    npx ai-agent-skills browse

# List all available skills
list:
    npx ai-agent-skills list

# List skills by category (development, document, creative, business, productivity, meta)
list-category category:
    npx ai-agent-skills list --category {{category}}

# List installed skills for an agent
list-installed agent="claude":
    npx ai-agent-skills list --installed --agent {{agent}}

# Search skills by name, description, or tags
search query:
    npx ai-agent-skills search "{{query}}"

# Show skill details
info skill:
    npx ai-agent-skills info {{skill}}

# Show/edit configuration
config:
    npx ai-agent-skills config

# Set default agent
config-default-agent agent:
    npx ai-agent-skills config --default-agent {{agent}}

# ═══════════════════════════════════════════════════════════════════════════════
# INSTALLATION - GENERIC
# ═══════════════════════════════════════════════════════════════════════════════

# Install skill (default agent)
install skill:
    npx ai-agent-skills install {{skill}}

# Install skill for specific agent
install-for skill agent:
    npx ai-agent-skills install {{skill}} --agent {{agent}}

# ═══════════════════════════════════════════════════════════════════════════════
# INSTALLATION - BY AGENT
# ═══════════════════════════════════════════════════════════════════════════════

# Install skill for Claude (default)
install-claude skill:
    npx ai-agent-skills install {{skill}} --agent claude

# Install skill for Cursor
install-cursor skill:
    npx ai-agent-skills install {{skill}} --agent cursor

# Install skill for Amp
install-amp skill:
    npx ai-agent-skills install {{skill}} --agent amp

# Install skill for VS Code / Copilot
install-vscode skill:
    npx ai-agent-skills install {{skill}} --agent vscode

# Install skill for Goose
install-goose skill:
    npx ai-agent-skills install {{skill}} --agent goose

# Install skill for Codex
install-codex skill:
    npx ai-agent-skills install {{skill}} --agent codex

# Install skill for Letta
install-letta skill:
    npx ai-agent-skills install {{skill}} --agent letta

# Install skill for project-local (.skills/)
install-project skill:
    npx ai-agent-skills install {{skill}} --agent project

# ═══════════════════════════════════════════════════════════════════════════════
# INSTALL FROM SOURCES
# ═══════════════════════════════════════════════════════════════════════════════

# Install from GitHub repo
install-github repo agent="claude":
    npx ai-agent-skills install {{repo}} --agent {{agent}}

# Install specific skill from GitHub repo
install-github-skill repo skill agent="claude":
    npx ai-agent-skills install {{repo}}/{{skill}} --agent {{agent}}

# Install from local path
install-local path agent="claude":
    npx ai-agent-skills install {{path}} --agent {{agent}}

# Dry run installation (preview only)
install-dry skill agent="claude":
    npx ai-agent-skills install {{skill}} --agent {{agent}} --dry-run

# ═══════════════════════════════════════════════════════════════════════════════
# UNINSTALL & UPDATE
# ═══════════════════════════════════════════════════════════════════════════════

# Uninstall skill
uninstall skill agent="claude":
    npx ai-agent-skills uninstall {{skill}} --agent {{agent}}

# Update specific skill
update skill agent="claude":
    npx ai-agent-skills update {{skill}} --agent {{agent}}

# Update all skills for an agent
update-all agent="claude":
    npx ai-agent-skills update --all --agent {{agent}}

# ═══════════════════════════════════════════════════════════════════════════════
# BULK INSTALL - POPULAR SKILLS
# ═══════════════════════════════════════════════════════════════════════════════

# Install core document skills
install-docs agent="claude":
    npx ai-agent-skills install pdf --agent {{agent}}
    npx ai-agent-skills install xlsx --agent {{agent}}
    npx ai-agent-skills install docx --agent {{agent}}
    npx ai-agent-skills install pptx --agent {{agent}}

# Install development skills
install-dev agent="claude":
    npx ai-agent-skills install frontend-design --agent {{agent}}
    npx ai-agent-skills install mcp-builder --agent {{agent}}
    npx ai-agent-skills install skill-creator --agent {{agent}}
    npx ai-agent-skills install webapp-testing --agent {{agent}}

# Install productivity skills
install-productivity agent="claude":
    npx ai-agent-skills install doc-coauthoring --agent {{agent}}
    npx ai-agent-skills install internal-comms --agent {{agent}}

# Install Anthropic's full skill set
install-anthropics agent="claude":
    npx ai-agent-skills install anthropics/skills --agent {{agent}}

# Install plurigrid ASI skills
install-plurigrid agent="claude":
    npx ai-agent-skills install plurigrid/asi --agent {{agent}}

# ═══════════════════════════════════════════════════════════════════════════════
# TRIPARTITE AGENT COORDINATION
# ═══════════════════════════════════════════════════════════════════════════════

# Install tripartite skills (Codex + Claude + Cursor)
install-tripartite:
    npx ai-agent-skills install unwiring-arena --agent codex
    npx ai-agent-skills install gay-mcp --agent claude
    npx ai-agent-skills install bisimulation-game --agent cursor

# Install gay-mcp on all agents
install-gay-mcp-all:
    npx ai-agent-skills install gay-mcp --agent claude
    npx ai-agent-skills install gay-mcp --agent cursor
    npx ai-agent-skills install gay-mcp --agent amp
    npx ai-agent-skills install gay-mcp --agent codex

# ═══════════════════════════════════════════════════════════════════════════════
# CLOJURESCRIPT TOOLS (via npx)
# ═══════════════════════════════════════════════════════════════════════════════

# Run nbb (Node Babashka) script
nbb script:
    npx nbb {{script}}

# Compile with Squint
squint-compile file:
    npx squint compile {{file}}

# Run with Squint
squint-run file:
    npx squint run {{file}}

# Compile with Cherry
cherry-compile file:
    npx cherry compile {{file}}

# ═══════════════════════════════════════════════════════════════════════════════
# TESTING TOOLS
# ═══════════════════════════════════════════════════════════════════════════════

# Install Playwright browsers
playwright-install:
    npx playwright install

# Install Playwright with deps
playwright-install-deps:
    npx playwright install --with-deps

# Run Playwright tests
playwright-test:
    npx playwright test

# Run specific Playwright test
playwright-test-file file:
    npx playwright test {{file}}

# Run Playwright in headed mode
playwright-headed:
    npx playwright test --headed

# Run Playwright UI mode
playwright-ui:
    npx playwright test --ui

# Show Playwright report
playwright-report:
    npx playwright show-report

# ═══════════════════════════════════════════════════════════════════════════════
# MCP TOOLS
# ═══════════════════════════════════════════════════════════════════════════════

# Run MCP Inspector
mcp-inspector:
    npx @modelcontextprotocol/inspector

# Create new MCP server
mcp-create name:
    npx @anthropic/create-mcp-server {{name}}

# Run Firecrawl MCP
firecrawl-mcp:
    npx -y firecrawl-mcp

# ═══════════════════════════════════════════════════════════════════════════════
# PROJECT MANAGEMENT
# ═══════════════════════════════════════════════════════════════════════════════

# Initialize ruler
ruler-init:
    npx ruler init

# Run CLI tests
test:
    node test.js

# Show agent paths
show-paths:
    @echo "Claude:  ~/.claude/skills/"
    @echo "Cursor:  .cursor/skills/"
    @echo "Amp:     ~/.amp/skills/"
    @echo "VS Code: .github/skills/"
    @echo "Goose:   ~/.config/goose/skills/"
    @echo "Codex:   ~/.codex/skills/"
    @echo "Letta:   ~/.letta/skills/"
    @echo "Project: .skills/"

# ═══════════════════════════════════════════════════════════════════════════════
# AUTOPOIESIS - Self-Modifying Configuration
# ═══════════════════════════════════════════════════════════════════════════════

# Initialize autopoiesis (DuckDB tracking)
autopoiesis-init:
    mkdir -p ~/.autopoiesis
    duckdb ~/.autopoiesis/config.duckdb -c "\
      CREATE TABLE IF NOT EXISTS config_log ( \
        id INTEGER PRIMARY KEY, \
        timestamp TIMESTAMP DEFAULT current_timestamp, \
        agent VARCHAR, \
        config_type VARCHAR, \
        key VARCHAR, \
        old_value JSON, \
        new_value JSON, \
        checksum VARCHAR \
      ); \
      CREATE TABLE IF NOT EXISTS skill_inventory ( \
        agent VARCHAR, \
        skill_name VARCHAR, \
        version VARCHAR, \
        installed_at TIMESTAMP DEFAULT current_timestamp, \
        trit INTEGER, \
        PRIMARY KEY (agent, skill_name) \
      );"
    @echo "✅ Autopoiesis initialized"

# Install skill to ALL agents
install-all skill:
    npx ai-agent-skills install {{skill}} --agent claude
    npx ai-agent-skills install {{skill}} --agent cursor
    npx ai-agent-skills install {{skill}} --agent amp
    npx ai-agent-skills install {{skill}} --agent codex
    npx ai-agent-skills install {{skill}} --agent vscode
    npx ai-agent-skills install {{skill}} --agent goose
    npx ai-agent-skills install {{skill}} --agent letta
    @echo "✅ {{skill}} installed to all agents"

# Propagate borkdude skills via nbb
propagate-borkdude:
    npx nbb skills/borkdude/propagate.clj

# ═══════════════════════════════════════════════════════════════════════════════
# RULER - Centralized Configuration
# ═══════════════════════════════════════════════════════════════════════════════

# Create ruler.toml template
ruler-config:
    @mkdir -p .ruler/skills .ruler/prompts .ruler/mcp .ruler/agents
    @echo '[ruler]' > .ruler/ruler.toml
    @echo 'version = "0.1.0"' >> .ruler/ruler.toml
    @echo 'source_of_truth = ".ruler/skills/"' >> .ruler/ruler.toml
    @echo '' >> .ruler/ruler.toml
    @echo '[agents]' >> .ruler/ruler.toml
    @echo 'claude = { path = "~/.claude/", skills = true, prompts = true }' >> .ruler/ruler.toml
    @echo 'codex = { path = "~/.codex/", skills = true, prompts = false }' >> .ruler/ruler.toml
    @echo 'cursor = { path = ".cursor/", skills = true, prompts = false }' >> .ruler/ruler.toml
    @echo 'amp = { path = "~/.amp/", skills = true, prompts = true }' >> .ruler/ruler.toml
    @echo 'vscode = { path = ".github/", skills = true, prompts = false }' >> .ruler/ruler.toml
    @echo 'goose = { path = "~/.config/goose/", skills = true, prompts = true }' >> .ruler/ruler.toml
    @echo '' >> .ruler/ruler.toml
    @echo '[propagation]' >> .ruler/ruler.toml
    @echo 'gf3_conservation = true' >> .ruler/ruler.toml
    @echo 'deterministic_colors = true' >> .ruler/ruler.toml
    @echo 'seed = 69420' >> .ruler/ruler.toml
    @echo '' >> .ruler/ruler.toml
    @echo '[mcp]' >> .ruler/ruler.toml
    @echo 'servers = ["gay", "firecrawl", "duckdb"]' >> .ruler/ruler.toml
    @echo "✅ Created .ruler/ruler.toml"

# Sync skills from ruler source of truth
ruler-sync:
    @echo "Syncing from .ruler/skills/ to all agents..."
    @for skill in $(ls .ruler/skills/ 2>/dev/null); do \
        just install-all $$skill; \
    done

# ═══════════════════════════════════════════════════════════════════════════════
# SYSTEM PROMPT MODIFICATION
# ═══════════════════════════════════════════════════════════════════════════════

# Modify Claude system prompt section
prompt-claude section content:
    npx nbb -e "(require '[clojure.string :as str]) \
      (let [path (str (System/getenv \"HOME\") \"/.claude/CLAUDE.md\") \
            marker (str \"<!-- autopoiesis:{{section}} -->\") \
            end-marker (str \"<!-- /autopoiesis:{{section}} -->\") \
            section-content (str marker \"\n\" \"{{content}}\" \"\n\" end-marker) \
            existing (try (slurp path) (catch Exception _ \"\")) \
            updated (if (str/includes? existing marker) \
                      (str/replace existing (re-pattern (str marker \"[\\\\s\\\\S]*?\" end-marker)) section-content) \
                      (str existing \"\n\n\" section-content))] \
        (spit path updated) \
        (println \"✅ Updated\" path))"

# Modify Codex instructions
prompt-codex section content:
    npx nbb -e "(let [path (str (System/getenv \"HOME\") \"/.codex/instructions.md\")] \
      (spit path (str (try (slurp path) (catch Exception _ \"\")) \"\n\n## {{section}}\n\n{{content}}\")) \
      (println \"✅ Updated\" path))"

# Modify Cursor rules
prompt-cursor content:
    @echo "{{content}}" >> .cursorrules
    @echo "✅ Appended to .cursorrules"

# ═══════════════════════════════════════════════════════════════════════════════
# MCP SERVER CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

# Add MCP server to Claude
mcp-add-claude name command args:
    npx nbb -e "(require '[cheshire.core :as json]) \
      (let [path (str (System/getenv \"HOME\") \"/.claude/mcp_servers.json\") \
            existing (try (json/parse-string (slurp path) true) (catch Exception _ {})) \
            updated (assoc existing \"{{name}}\" {:type \"stdio\" :command \"{{command}}\" :args [{{args}}]})] \
        (spit path (json/generate-string updated {:pretty true})) \
        (println \"✅ Added {{name}} to Claude MCP config\"))"

# Add gay-mcp to all agents
mcp-add-gay:
    @echo "Adding gay-mcp server to all agents..."
    just mcp-add-claude gay julia "--project=~/.julia/packages/Gay -e \"using Gay; Gay.serve_mcp()\""

# Add firecrawl-mcp
mcp-add-firecrawl:
    just mcp-add-claude firecrawl npx "-y firecrawl-mcp"

# ═══════════════════════════════════════════════════════════════════════════════
# DUCKDB CONFIGURATION TRACKING
# ═══════════════════════════════════════════════════════════════════════════════

# Query configuration history
config-history limit="20":
    duckdb ~/.autopoiesis/config.duckdb -c "SELECT timestamp, agent, config_type, key FROM config_log ORDER BY timestamp DESC LIMIT {{limit}}"

# Query skill inventory
skill-inventory:
    duckdb ~/.autopoiesis/config.duckdb -c "SELECT agent, skill_name, version, trit FROM skill_inventory ORDER BY agent, skill_name"

# Log a configuration change
config-log agent config_type key old_value new_value:
    duckdb ~/.autopoiesis/config.duckdb -c "INSERT INTO config_log (agent, config_type, key, old_value, new_value) VALUES ('{{agent}}', '{{config_type}}', '{{key}}', '{{old_value}}', '{{new_value}}')"

# Register skill installation
skill-register agent skill version trit="0":
    duckdb ~/.autopoiesis/config.duckdb -c "INSERT OR REPLACE INTO skill_inventory (agent, skill_name, version, trit) VALUES ('{{agent}}', '{{skill}}', '{{version}}', {{trit}})"

# ═══════════════════════════════════════════════════════════════════════════════
# VERS VM DEPLOYMENT (hdresearch/duck patterns)
# ═══════════════════════════════════════════════════════════════════════════════

# Deploy autopoiesis to Vers VM
vers-deploy-autopoiesis vm_id:
    @echo "🚀 Deploying autopoiesis to VM {{vm_id}}..."
    vers execute {{vm_id}} "apt-get update && apt-get install -y curl git jq"
    vers execute {{vm_id}} "curl -LsSf https://astral.sh/uv/install.sh | sh"
    vers execute {{vm_id}} "npm install -g nbb ai-agent-skills"
    vers execute {{vm_id}} "~/.local/bin/uv pip install --system duckdb"
    vers execute {{vm_id}} "npx ruler init"
    vers execute {{vm_id}} "npx ai-agent-skills install plurigrid/asi --agent codex"
    @echo "✅ Autopoiesis deployed to {{vm_id}}"

# Run nbb script on Vers VM
vers-nbb vm_id script:
    vers execute {{vm_id}} "nbb {{script}}"

# Query Vers VM history via DuckDB
vers-duck-query vm_id sql:
    vers execute {{vm_id}} "duckdb -json -c \"{{sql}}\""

# Install ai-agent-skills on Vers VM
vers-install-skills vm_id:
    vers execute {{vm_id}} "npm install -g nbb ai-agent-skills"

# ═══════════════════════════════════════════════════════════════════════════════
# TRIPARTITE AUTOPOIESIS
# ═══════════════════════════════════════════════════════════════════════════════

# Deploy autopoiesis across tripartite agents
install-tripartite-autopoiesis:
    npx ai-agent-skills install autopoiesis --agent codex
    npx ai-agent-skills install autopoiesis --agent claude
    npx ai-agent-skills install autopoiesis --agent cursor
    npx ai-agent-skills install gay-mcp --agent codex
    npx ai-agent-skills install gay-mcp --agent claude
    npx ai-agent-skills install gay-mcp --agent cursor
    npx ai-agent-skills install bisimulation-game --agent codex
    npx ai-agent-skills install bisimulation-game --agent claude
    npx ai-agent-skills install bisimulation-game --agent cursor
    @echo "✅ Tripartite autopoiesis deployed"

# ═══════════════════════════════════════════════════════════════════════════════
# ONE-LINERS (The Power of Autopoiesis)
# ═══════════════════════════════════════════════════════════════════════════════

# Quick: Add context to Claude
quick-context context:
    just prompt-claude context "{{context}}"

# Quick: Install skill everywhere
quick-skill skill:
    just install-all {{skill}}

# Quick: Full autopoiesis setup
quick-setup:
    just autopoiesis-init
    just ruler-config
    just install-tripartite-autopoiesis
    @echo "✅ Full autopoiesis setup complete"

# ═══════════════════════════════════════════════════════════════════════════════
# AI-AGENT-SKILLS ADVANCED (via nbb)
# ═══════════════════════════════════════════════════════════════════════════════

# Show available skill bundles
bundles:
    npx nbb skills/autopoiesis/ai-agent-skills.cljs bundles

# Show all agents status
status:
    npx nbb skills/autopoiesis/ai-agent-skills.cljs status

# Install bundle to agent (docs, dev, creative, productivity, tripartite, core)
bundle name agent="claude":
    npx nbb skills/autopoiesis/ai-agent-skills.cljs bundle {{name}} {{agent}}

# Install bundle to ALL agents
bundle-all name:
    npx nbb skills/autopoiesis/ai-agent-skills.cljs bundle-all {{name}}

# Matrix install (comma-separated skills × agents)
matrix skills agents:
    npx nbb skills/autopoiesis/ai-agent-skills.cljs matrix "{{skills}}" "{{agents}}"

# Compare installed skills between two agents
diff agent1 agent2:
    npx nbb skills/autopoiesis/ai-agent-skills.cljs diff {{agent1}} {{agent2}}

# ═══════════════════════════════════════════════════════════════════════════════
# QUICK RECIPES
# ═══════════════════════════════════════════════════════════════════════════════

# Install core skills to tripartite agents (Claude + Codex + Cursor)
quick-tripartite:
    just matrix "gay-mcp,autopoiesis,bisimulation-game" "claude,codex,cursor"

# Install docs bundle to Claude
quick-docs:
    just bundle docs claude

# Install dev bundle to all agents
quick-dev-all:
    just bundle-all dev

# Full plurigrid ASI setup
quick-plurigrid:
    just quick-setup
    just bundle-all core
    @echo "✅ Full Plurigrid ASI setup complete"

# ═══════════════════════════════════════════════════════════════════════════════
# MAXIMAL PROPAGATION - Install Everything Everywhere
# ═══════════════════════════════════════════════════════════════════════════════

# MAXIMAL: Install autopoiesis + all core skills to ALL agents
propagate:
    @echo "╔═══════════════════════════════════════════════════════════════════════════════╗"
    @echo "║  MAXIMAL PROPAGATION - Installing to ALL agents                               ║"
    @echo "╚═══════════════════════════════════════════════════════════════════════════════╝"
    @echo ""
    @echo "→ Installing autopoiesis..."
    npx ai-agent-skills install autopoiesis --agent claude
    npx ai-agent-skills install autopoiesis --agent cursor
    npx ai-agent-skills install autopoiesis --agent amp
    npx ai-agent-skills install autopoiesis --agent codex
    npx ai-agent-skills install autopoiesis --agent vscode
    npx ai-agent-skills install autopoiesis --agent goose
    npx ai-agent-skills install autopoiesis --agent letta
    npx ai-agent-skills install autopoiesis --agent project
    @echo ""
    @echo "→ Installing gay-mcp..."
    npx ai-agent-skills install gay-mcp --agent claude
    npx ai-agent-skills install gay-mcp --agent cursor
    npx ai-agent-skills install gay-mcp --agent amp
    npx ai-agent-skills install gay-mcp --agent codex
    npx ai-agent-skills install gay-mcp --agent vscode
    npx ai-agent-skills install gay-mcp --agent goose
    npx ai-agent-skills install gay-mcp --agent letta
    npx ai-agent-skills install gay-mcp --agent project
    @echo ""
    @echo "→ Installing bisimulation-game..."
    npx ai-agent-skills install bisimulation-game --agent claude
    npx ai-agent-skills install bisimulation-game --agent cursor
    npx ai-agent-skills install bisimulation-game --agent amp
    npx ai-agent-skills install bisimulation-game --agent codex
    npx ai-agent-skills install bisimulation-game --agent vscode
    npx ai-agent-skills install bisimulation-game --agent goose
    npx ai-agent-skills install bisimulation-game --agent letta
    npx ai-agent-skills install bisimulation-game --agent project
    @echo ""
    @echo "→ Installing duckdb-temporal-versioning..."
    npx ai-agent-skills install duckdb-temporal-versioning --agent claude
    npx ai-agent-skills install duckdb-temporal-versioning --agent cursor
    npx ai-agent-skills install duckdb-temporal-versioning --agent amp
    npx ai-agent-skills install duckdb-temporal-versioning --agent codex
    npx ai-agent-skills install duckdb-temporal-versioning --agent vscode
    npx ai-agent-skills install duckdb-temporal-versioning --agent goose
    npx ai-agent-skills install duckdb-temporal-versioning --agent letta
    npx ai-agent-skills install duckdb-temporal-versioning --agent project
    @echo ""
    @echo "→ Installing triad-interleave..."
    npx ai-agent-skills install triad-interleave --agent claude
    npx ai-agent-skills install triad-interleave --agent cursor
    npx ai-agent-skills install triad-interleave --agent amp
    npx ai-agent-skills install triad-interleave --agent codex
    npx ai-agent-skills install triad-interleave --agent vscode
    npx ai-agent-skills install triad-interleave --agent goose
    npx ai-agent-skills install triad-interleave --agent letta
    npx ai-agent-skills install triad-interleave --agent project
    @echo ""
    @echo "✅ MAXIMAL PROPAGATION COMPLETE"
    @echo "   5 skills × 8 agents = 40 installations"

# Propagate single skill to ALL agents
propagate-skill skill:
    @echo "→ Propagating {{skill}} to all agents..."
    npx ai-agent-skills install {{skill}} --agent claude
    npx ai-agent-skills install {{skill}} --agent cursor
    npx ai-agent-skills install {{skill}} --agent amp
    npx ai-agent-skills install {{skill}} --agent codex
    npx ai-agent-skills install {{skill}} --agent vscode
    npx ai-agent-skills install {{skill}} --agent goose
    npx ai-agent-skills install {{skill}} --agent letta
    npx ai-agent-skills install {{skill}} --agent project
    @echo "✅ {{skill}} propagated to 8 agents"

# Propagate multiple skills (space-separated)
propagate-skills +skills:
    @for skill in {{skills}}; do just propagate-skill $$skill; done

# Propagate from plurigrid/asi repo
propagate-repo:
    @echo "→ Propagating entire plurigrid/asi repo..."
    npx ai-agent-skills install plurigrid/asi --agent claude
    npx ai-agent-skills install plurigrid/asi --agent cursor
    npx ai-agent-skills install plurigrid/asi --agent amp
    npx ai-agent-skills install plurigrid/asi --agent codex
    npx ai-agent-skills install plurigrid/asi --agent vscode
    npx ai-agent-skills install plurigrid/asi --agent goose
    npx ai-agent-skills install plurigrid/asi --agent letta
    @echo "✅ plurigrid/asi propagated to 7 agents"

# NUCLEAR: Everything from anthropics + plurigrid to all agents
propagate-nuclear:
    @echo "☢️  NUCLEAR PROPAGATION - This will take a while..."
    just propagate
    just propagate-skill frontend-design
    just propagate-skill mcp-builder
    just propagate-skill skill-creator
    just propagate-skill pdf
    just propagate-skill xlsx
    just propagate-skill docx
    just propagate-skill pptx
    just propagate-skill webapp-testing
    just propagate-skill code-review
    just propagate-skill doc-coauthoring
    @echo ""
    @echo "☢️  NUCLEAR PROPAGATION COMPLETE"
    @echo "   16 skills × 8 agents = 128 installations"

# Install complete Aptos Society / Agent-O-Rama system
society:
    #!/usr/bin/env bash
    set -e
    echo "🌐 Installing Aptos Society..."
    
    # Download bundle from GitHub
    curl -sL "https://github.com/plurigrid/asi/raw/aptos-society-bundle/aptos_society.tar.gz" -o /tmp/aptos_society.tar.gz
    
    # Extract to home (excludes keys by design)
    tar xzf /tmp/aptos_society.tar.gz -C ~
    
    # Generate fresh keys + MCP config
    echo "🔑 Generating fresh Aptos wallets..."
    bb ~/.agents/scripts/create-aptos-worlds.bb
    
    echo "⚙️  Configuring MCP servers..."
    bb ~/.agents/scripts/generate-mcp-config.bb
    
    echo ""
    echo "✅ Aptos Society installed!"
    echo "   28 wallets in ~/.aptos/worlds/"
    echo "   Skills in ~/.agents/skills/ + ~/.claude/skills/"
    echo "   GayMove contracts in ~/.topos/GayMove/"
    echo "   Agent core in ~/agent-o-rama/src/"
