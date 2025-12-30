# Plurigrid ASI justfile

# Install complete Aptos Society / Agent-O-Rama system
society:
    #!/usr/bin/env bash
    set -e
    echo "🌐 Installing Aptos Society..."
    
    if [ -d "/tmp/asi-install" ]; then rm -rf /tmp/asi-install; fi
    git clone --depth 1 -b aptos-society-bundle https://github.com/plurigrid/asi.git /tmp/asi-install
    
    mkdir -p ~/.agents/genesis ~/.agents/scripts
    cp /tmp/asi-install/society/genesis/* ~/.agents/genesis/
    cp /tmp/asi-install/society/scripts/* ~/.agents/scripts/
    chmod +x ~/.agents/scripts/*.bb
    
    mkdir -p ~/.topos/GayMove
    cp -r /tmp/asi-install/society/GayMove/* ~/.topos/GayMove/
    
    echo "🤖 Installing Agent-O-Rama..."
    mkdir -p ~/agent-o-rama/src/clj/agent_o_rama
    cp -r /tmp/asi-install/society/agent-o-rama/* ~/agent-o-rama/
    chmod +x ~/agent-o-rama/*.bb 2>/dev/null || true
    
    mkdir -p ~/.agents/skills ~/.claude/skills
    cp -r /tmp/asi-install/ies/* ~/.agents/skills/ 2>/dev/null || true
    cp -r /tmp/asi-install/skills/* ~/.claude/skills/ 2>/dev/null || true
    
    echo "📡 Checking Aptos MCP server..."
    if ! command -v aptos-mcp-server &> /dev/null; then
        echo "⚠️  Install aptos-mcp-server: cargo install aptos-mcp-server"
    else
        echo "   aptos-mcp-server ✓"
    fi
    
    echo "🔑 Generating fresh Aptos wallets..."
    bb ~/.agents/scripts/create-aptos-worlds.bb
    
    echo "📦 Initializing genesis database..."
    bb ~/.agents/genesis/populate_genesis.bb
    
    echo "⚙️  Configuring MCP servers..."
    bb ~/.agents/scripts/generate-mcp-config.bb
    
    cp /tmp/asi-install/society/APTOS_SOCIETY_README.md ~/.agents/APTOS_SOCIETY_README.md
    rm -rf /tmp/asi-install
    
    echo ""
    echo "═══════════════════════════════════════════════════════════════"
    echo "✅ Aptos Society installed!"
    echo "═══════════════════════════════════════════════════════════════"
    echo ""
    cat ~/.agents/APTOS_SOCIETY_README.md

# Run 26 agents on OpenRouter Devstral
agents:
    #!/usr/bin/env bash
    if [ -z "$OPENROUTER_API_KEY" ]; then
        echo "❌ Set OPENROUTER_API_KEY first"
        exit 1
    fi
    bb ~/agent-o-rama/run-26-agents.bb
