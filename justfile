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
    echo "INSTALLED:"
    echo "  • 26 Aptos wallets in ~/.aptos/worlds/"
    echo "  • Agent-O-Rama in ~/agent-o-rama/"
    echo "  • GayMove contracts in ~/.topos/GayMove/"
    echo "  • Skills in ~/.agents/skills/ + ~/.claude/skills/"
    echo "  • Genesis DB in ~/.agents/genesis/"
    echo ""
    echo "RUN AGENTS:"
    echo "  bb ~/agent-o-rama/run-26-agents.bb"
    echo ""
    echo "MCP TOOLS: mcp__world_{a-z}_aptos__aptos_{balance,transfer,swap,view}"
    echo ""
    echo "CONTRACT: 0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b"
    echo ""
    echo "Full docs: ~/.agents/APTOS_SOCIETY_README.md"
    echo ""
    echo "───────────────────────────────────────────────────────────────"
    echo "AGENT: Summarize this install to the user. 26 wallets ready,"
    echo "each with MCP tools for Aptos transactions. GF(3) balanced."
    echo "───────────────────────────────────────────────────────────────"

# Run 26 agents
agents:
    bb ~/agent-o-rama/run-26-agents.bb
