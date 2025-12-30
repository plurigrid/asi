# Plurigrid ASI justfile

# Install complete Aptos Society / Agent-O-Rama system
society:
    #!/usr/bin/env bash
    set -e
    echo "🌐 Installing Aptos Society..."
    
    if [ -d "/tmp/asi-install" ]; then rm -rf /tmp/asi-install; fi
    git clone --depth 1 -b aptos-society-bundle https://github.com/plurigrid/asi.git /tmp/asi-install
    
    # Genesis + scripts + skills
    mkdir -p ~/.agents/genesis ~/.agents/scripts ~/.agents/skills
    cp /tmp/asi-install/society/genesis/* ~/.agents/genesis/
    cp /tmp/asi-install/society/scripts/* ~/.agents/scripts/
    cp -r /tmp/asi-install/skills/* ~/.agents/skills/ 2>/dev/null || true
    chmod +x ~/.agents/scripts/*.bb
    
    # Aptos: GayMove + agent-o-rama
    mkdir -p ~/.aptos/GayMove ~/.aptos/agent-o-rama
    cp -r /tmp/asi-install/society/GayMove/* ~/.aptos/GayMove/
    cp -r /tmp/asi-install/society/agent-o-rama/* ~/.aptos/agent-o-rama/
    chmod +x ~/.aptos/agent-o-rama/*.bb 2>/dev/null || true
    
    echo "📡 Checking dependencies..."
    command -v bb &>/dev/null || echo "⚠️  Install babashka: brew install borkdude/brew/babashka"
    command -v aptos-mcp-server &>/dev/null && echo "   aptos-mcp-server ✓" || echo "⚠️  Install: cargo install aptos-mcp-server"
    
    echo "🔑 Generating fresh Aptos wallets..."
    bb ~/.agents/scripts/create-aptos-worlds.bb
    
    echo "📦 Initializing genesis database..."
    bb ~/.agents/genesis/populate_genesis.bb
    
    echo "⚙️  Configuring MCP servers..."
    bb ~/.agents/scripts/generate-mcp-config.bb
    
    cp /tmp/asi-install/society/APTOS_SOCIETY_README.md ~/.aptos/README.md
    rm -rf /tmp/asi-install
    
    echo ""
    echo "═══════════════════════════════════════════════════════════════"
    echo "✅ APTOS SOCIETY INSTALLED"
    echo "═══════════════════════════════════════════════════════════════"
    echo ""
    cat ~/.aptos/README.md
    echo ""
    echo "═══════════════════════════════════════════════════════════════"
    echo "README:      cat ~/.aptos/README.md"
    echo "Run agents:  just agents"
    echo "═══════════════════════════════════════════════════════════════"

# Run 26 agents
agents:
    bb ~/.aptos/agent-o-rama/run-26-agents.bb

# Show README
readme:
    cat ~/.aptos/README.md
