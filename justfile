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
    
    # Install GayMove
    mkdir -p ~/.topos/GayMove
    cp -r /tmp/asi-install/society/GayMove/* ~/.topos/GayMove/
    
    # Install skills from ies/
    mkdir -p ~/.agents/skills ~/.claude/skills
    cp -r /tmp/asi-install/ies/* ~/.agents/skills/ 2>/dev/null || true
    cp -r /tmp/asi-install/skills/* ~/.claude/skills/ 2>/dev/null || true
    
    # Generate fresh keys + MCP config
    echo "🔑 Generating fresh Aptos wallets..."
    bb ~/.agents/scripts/create-aptos-worlds.bb
    
    echo "⚙️  Configuring MCP servers..."
    bb ~/.agents/scripts/generate-mcp-config.bb
    
    # Cleanup
    rm -rf /tmp/asi-install
    
    echo ""
    echo "✅ Aptos Society installed!"
    echo "   28 wallets in ~/.aptos/worlds/"
    echo "   Genesis DB: bb ~/.agents/genesis/populate_genesis.bb"
    echo "   Skills in ~/.agents/skills/ + ~/.claude/skills/"
    echo "   GayMove contracts in ~/.topos/GayMove/"
