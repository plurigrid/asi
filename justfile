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
    
    echo "📡 Checking dependencies..."
    command -v bb &>/dev/null || echo "⚠️  Install babashka: brew install borkdude/brew/babashka"
    command -v aptos-mcp-server &>/dev/null && echo "   aptos-mcp-server ✓" || echo "⚠️  Install: cargo install aptos-mcp-server"
    
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
    echo "✅ APTOS SOCIETY INSTALLED"
    echo "═══════════════════════════════════════════════════════════════"
    echo ""
    cat ~/.agents/APTOS_SOCIETY_README.md
    echo ""
    echo "═══════════════════════════════════════════════════════════════"
    echo "To view this README again:  cat ~/.agents/APTOS_SOCIETY_README.md"
    echo "To run 26 agents:           just agents"
    echo "═══════════════════════════════════════════════════════════════"

# Run 26 agents
agents:
    #!/usr/bin/env bash
    bb ~/agent-o-rama/run-26-agents.bb

# Show README
readme:
    cat ~/.agents/APTOS_SOCIETY_README.md
