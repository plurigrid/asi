# Skill Installation Manifest
Generated: $(date)

## Summary
- **Total Skills Installed**: 33
- **Target Agents**: 5 (claude, amp, cursor, copilot, codex)
- **Total Installations**: 165 (33 skills × 5 agents)
- **Installation Date**: 2025-12-21

## Agent Configurations

### Claude
- **Location**: `.claude/`
- **Skill Directory**: `.claude/skills/` (33 skills)
- **MCP Config**: `.claude/mcp.json`
- **Status**: ✓ Fully Installed

### Amp
- **Location**: Root `.ruler/`
- **Skill Directory**: `.ruler/skills/` (33 skills - main registry)
- **MCP Config**: `.mcp.json`
- **Status**: ✓ Fully Installed

### Cursor
- **Location**: `.cursor/`
- **Skill Directory**: `.cursor/skills/` (33 skills)
- **MCP Config**: `.cursor/mcp.json`
- **Status**: ✓ Fully Installed

### Copilot
- **Location**: `.vscode/`
- **Skill Directory**: `.vscode/skills/` (33 skills)
- **MCP Config**: `.vscode/mcp.json`
- **Status**: ✓ Fully Installed

### Codex
- **Location**: `.codex/`
- **Skill Directory**: `.codex/skills/` (33 skills)
- **MCP Config**: `.codex/mcp.json`
- **Status**: ✓ Fully Installed

## Installed Skills (33 Total)

1. **acsets** - Abstract Chemical Sets
2. **bdd-mathematical-verification** - BDD Mathematical Verification
3. **bisimulation-game** - Bisimulation Game
4. **bmorphism-stars** - B-Morphism Stars
5. **borkdude** - ClojureScript Runtime Selection
6. **cider-clojure** - CIDER Clojure Development
7. **cider-embedding** - CIDER Embedding
8. **clj-kondo-3color** - clj-kondo 3-Color
9. **codex-self-rewriting** - Codex Self-Rewriting
10. **crdt** - CRDT Memoization System
11. **duckdb-temporal-versioning** - DuckDB Temporal Versioning
12. **epistemic-arbitrage** - Epistemic Arbitrage
13. **frontend-design** - Frontend Design
14. **gay-mcp** - GAY.jl Deterministic Colors (MCP Server)
15. **geiser-chicken** - Geiser Chicken Scheme
16. **glass-bead-game** - Glass Bead Game (Hesse)
17. **hatchery-papers** - Hatchery Papers
18. **mathpix-ocr** - Mathpix OCR
19. **proofgeneral-narya** - ProofGeneral Narya
20. **rama-gay-clojure** - Rama GAY Clojure
21. **reafference-corollary-discharge** - Reafference & Corollary Discharge (von Holst)
22. **rubato-composer** - Rubato Composer
23. **self-validation-loop** - Self-Validation Loop
24. **slime-lisp** - SLIME Lisp
25. **spi-parallel-verify** - SPI Parallel Verification
26. **squint-runtime** - Squint Runtime
27. **tailscale-file-transfer** - Tailscale File Transfer
28. **three-match** - 3-Match (3-SAT via Subgraph Isomorphism)
29. **triad-interleave** - Triad Interleave
30. **unworld** - Unworld (Replace Time with Color Chains)
31. **unworlding-involution** - Unworlding Involution
32. **world-hopping** - World Hopping
33. **xenodium-elisp** - Xenodium Elisp

## MCP Servers Configured

### Local MCP Servers
- **gay**: Julia-based deterministic color generation (SplitMix64 + golden angle)
- **glass-bead-game**: Ruby-based Hesse-inspired game
- **skillz**: Skill loading and management

### External MCP Servers
- **firecrawl**: Web scraping and crawling
- **exa**: AI-powered web search
- **tree-sitter**: AST-based code analysis

## Installation Verification

All agents have been verified to have:
- ✓ Skills directory created with proper structure
- ✓ All 33 skills installed (symlinked or copied)
- ✓ Valid JSON MCP configuration files
- ✓ MCP server definitions for gay, glass-bead-game, firecrawl, exa, tree-sitter, and skillz

## Next Steps

1. Test skill availability in each agent
2. Load and validate MCP server configurations
3. Run agent-specific skill discovery procedures
4. Document agent-specific behavior with each skill

## Notes

- Skills are symlinked to save disk space where possible
- MCP configurations use environment variable substitution for API keys
- All agents share the same skill definitions from `.ruler/skills/`
- Agent-specific configurations in `.claude/`, `.cursor/`, `.vscode/`, `.codex/` for agent-specific behavior

