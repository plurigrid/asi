# Plurigrid ASI justfile

# Install complete Aptos Society / Agent-O-Rama system
society:
    #!/usr/bin/env bash
    set -e
    echo "🌐 Installing Aptos Society..."
    
    # Clone/update asi repo
    if [ -d "/tmp/asi-install" ]; then rm -rf /tmp/asi-install; fi
    git clone --depth 1 -b aptos-society-bundle https://github.com/plurigrid/asi.git /tmp/asi-install
    
    # Install genesis
    mkdir -p ~/.agents/genesis ~/.agents/scripts
    cp /tmp/asi-install/society/genesis/* ~/.agents/genesis/
    cp /tmp/asi-install/society/scripts/* ~/.agents/scripts/
    chmod +x ~/.agents/scripts/*.bb
    
    # Install GayMove
    mkdir -p ~/.topos/GayMove
    cp -r /tmp/asi-install/society/GayMove/* ~/.topos/GayMove/
    
    # Install agent-o-rama
    echo "🤖 Installing Agent-O-Rama..."
    mkdir -p ~/agent-o-rama/src/clj/agent_o_rama
    cp -r /tmp/asi-install/society/agent-o-rama/* ~/agent-o-rama/
    
    # Install skills
    mkdir -p ~/.agents/skills ~/.claude/skills
    cp -r /tmp/asi-install/ies/* ~/.agents/skills/ 2>/dev/null || true
    cp -r /tmp/asi-install/skills/* ~/.claude/skills/ 2>/dev/null || true
    
    # Install aptos-mcp-server if not present
    echo "📡 Installing Aptos MCP server..."
    if ! command -v aptos-mcp-server &> /dev/null; then
        if command -v cargo &> /dev/null; then
            cargo install aptos-mcp-server 2>/dev/null || echo "⚠️  Install manually: cargo install aptos-mcp-server"
        elif command -v npm &> /dev/null; then
            npm install -g @anthropics/aptos-mcp-server 2>/dev/null || echo "⚠️  Install manually from npm or cargo"
        else
            echo "⚠️  Install aptos-mcp-server: cargo install aptos-mcp-server"
        fi
    else
        echo "   aptos-mcp-server already installed"
    fi
    
    # Generate fresh wallets
    echo "🔑 Generating fresh Aptos wallets..."
    bb ~/.agents/scripts/create-aptos-worlds.bb
    
    # Initialize genesis DB
    echo "📦 Initializing genesis database..."
    bb ~/.agents/genesis/populate_genesis.bb
    
    # Configure MCP servers
    echo "⚙️  Configuring MCP servers..."
    bb ~/.agents/scripts/generate-mcp-config.bb
    
    # Install README
    cp /tmp/asi-install/society/APTOS_SOCIETY_README.md ~/.agents/APTOS_SOCIETY_README.md
    
    # Cleanup
    rm -rf /tmp/asi-install
    
    echo ""
    echo "═══════════════════════════════════════════════════════════════"
    echo "✅ Aptos Society installed!"
    echo "═══════════════════════════════════════════════════════════════"
    echo ""
    cat ~/.agents/APTOS_SOCIETY_README.md
