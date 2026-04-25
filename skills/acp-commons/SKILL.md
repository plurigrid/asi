---
name: acp-commons
description: "Atlas of Agent Client Protocol (ACP) clients, agents, and OCapN/CapTP-grounded actors. Use when picking a coding agent surface, threading ACP over CapTP, locating the local Zoad implementation, or navigating the Hermes-as-OCapN-actor family."
---

# acp-commons

Third nested atlas in the family. Navigates the **protocol-substrate** layer of the Para-mensch atom: which ACP client / agent surface carries a given Para(Optic) interaction.

- `repl-commons` — runtime-substrate (which REPL backend?)
- `para-mensch-commons` — categorical-substrate (which Para(Optic) instantiation?)
- **`acp-commons` (this skill) — protocol-substrate** (which ACP client × CapTP wire?)

## The atom in protocol form

```
                client                agent
              ┌────────┐            ┌──────────┐
       ε ────►│        │  prompt    │          │
   user input │  Para- │ ─────────► │  agent   │── tool → S (FS/PTY/MCP)
              │ mensch │            │ subproc  │     │
       T ◄────│  port  │  stream    │          │ ◄───┘ residual M
              │        │ ◄───────── │          │       (audit, GF(3) trit)
              └────────┘            └──────────┘
                  │                       ▲
                  └──── parameter P ──────┘
                  (session id, sturdy ref, capabilities)
```

Play (▷) = forward prompt → tool calls.
Witness (◇) = streamed plan/thought/tool-update audit + permission UI's declared loss.
Coplay (◁) = parameter feedback through session/permission updates and BCom-style updates over CapTP.

## Tier 1 — reference / production-grade clients

### Zed
Native ACP IDE loop (not sidecar). Reference editor client. ACP traffic is a first-class buffer-and-action surface.

### Toad (Python original)
Local clone at `/tmp/batrachianai-toad/`. Terminal-native ACP workbench: PTY + ACP subprocess + session lifecycle + SQLite persistence + permission UI + concurrent sessions + diffs. Key files: `src/toad/acp/agent.py:1`, `src/toad/widgets/conversation.py:264`, `src/toad/widgets/terminal_tool.py:1`. **Furthest unique = terminal-native ACP workbench**.

### Zoad (Zig port)
Local at `/Users/bob/i/zoad/`. Pixel-perfect Zig 0.16.0-dev reimplementation of Toad. **1772 LOC, builds clean, no deps**. Modules: `src/{main,style}.zig` (713 LOC) + `src/acp/{protocol,jsonrpc,agent}.zig` (795 LOC; `agent.zig:AgentState` is the 8-state ACP residual FSM) + `src/widgets/{throbber,conversation,sidebar,prompt}.zig` (977 LOC). Mach-O arm64 binary at `zig-out/bin/zoad`. NOT under git. Embedded variant in `/Users/bob/i/zig-syrup/src/zoad.zig` (693 LOC) uses retty + Syrup transport + notcurses; positions Zoad as a Plurigrid Human Vat holding SturdyRefs.

### VS Code ACP Client
Full FS / terminal / permissions + traffic logging. Furthest unique = ACP-traffic debug visibility.

### JetBrains AI Assistant ACP
`~/.jetbrains/acp.json` subprocess agents + IDEA MCP bridging. Furthest unique = ACP+MCP tool governance.

## Tier 2 — distinctive surface

- **Jockey** — multi-agent orchestrator (Claude Code + Gemini CLI + Codex CLI). Client-as-scheduler.
- **SuperQode** — agentic coding product.
- **Neovim** — `CodeCompanion`, `agentic.nvim`, `avante.nvim` — modal/editor composability.
- **AionUi / aizen / DeepChat / Tidewave** — reusable app/browser ACP frontends.
- **marimo / agent-client-kernel / DuckDB sidequery ACP** — notebook/dataframe/db substrate.

## Tier 3 — niche / extensibility

- **Emacs** — `agent-shell.el` / `acp.el` — Lisp-extensible ACP workflows.
- **Obsidian Agent Client / Minion Mind** — note-graph/vault context.
- **Unity ACP / Unity Agent Client** — game-editor scene context.
- Long-tail: Chrome ACP / acpx / gemini-cli-desktop / Agent Studio / iflow-cli / Lody / Mitto / Nori CLI / Ngent / RayClaw / RLM Code.
- **Mobile**: Agmente / Ferngeist / Happy / Mobvibe.
- **Messaging**: ACP Discord, duckdb-claude-slack, Juan, OpenACP, Telegram ACP Bot, Telegram-ACP, WeChat ACP.

## ACP-over-CapTP (the OCapN bridge)

ACP-as-prompt-stream wraps cleanly over CapTP-as-cap-passing. The translation:

| ACP | CapTP / OCapN |
|---|---|
| session id | sturdy ref |
| permission grant | bcom-style attestation |
| tool call | message-pass to a sealed reference |
| MCP server | far-vat with restricted promise pipelining |
| agent subprocess | spawned vat with its own gc |

Local skills carrying this bridge:

`teglon-acp` · `captp` · `goblins` · `goblins-adapter` · `guile-goblins-hoot` · `wasm-goblins` · `openclaw-goblins-adapter` · `universal-captp-derivation` · `google-cloud-ocapn-vats` · `syrup` · `zig-syrup-propagator-interleave` · `shadow-goblin` · `dynamic-sufficiency-goblin`

Primary entries: `captp` (wire), `goblins` (vat runtime), `universal-captp-derivation` (constructive proof of the bridge), `teglon-acp` (the Plurigrid-side ACP), `toad-telemetry` (run-time audit of an ACP session).

## Hermes-as-OCapN-actor (planned)

The 12-skill `hermes-*` family stages an LLM agent's standard tools (`fs`, `net`, `mcp`, `mem`, `tool`, `cron`, `cred`, `session`, `approval`, `ctx-engine`) as **sealed CapTP capabilities**:

- `hermes-acp-over-captp` — the bridge proper
- `hermes-fs-as-cap`, `hermes-net-as-cap`, `hermes-tool-as-cap`, `hermes-mcp-as-sealed`
- `hermes-mem-as-dataspace`, `hermes-cron-as-dataspace`
- `hermes-approval-as-revocable`, `hermes-cred-as-sturdy`
- `hermes-session-as-snapshot`, `hermes-ctx-engine-shim`, `hermes-goblins-bridge`

Currently a WIP family (untracked on `wev-hodge-decomp`). Once landed, the pattern `hermes-*` adds them all to this hub in one edit.

## Frameworks (NOT clients)

`AgentPool` · `fast-agent-acp` · `Koog` · `LangChain/LangGraph Deep Agents ACP` · `LlamaIndex workflows-acp` · `LLMling-Agent` · `AgentRQ` · `Aptove Bridge` · `OpenClaw bridge` · `stdio Bus`. fast-agent has unusually complete ACP feature coverage but is agent/framework-side. `openclaw-goblins-adapter` is the local OpenClaw bridge skill.

## yb-translator parable for ACP

```
CONCEPT: ACP-over-CapTP bridge
BIOLOGY: hormone-receptor signaling with cAMP second messenger
ONTOLOGY: GO — signal transduction (GO:0007165),
          G protein-coupled receptor signaling pathway (GO:0007186)
EXAMPLE: ACP session-id ≡ ligand binding event;
         CapTP sturdy-ref ≡ activated GαS;
         ACP tool-stream ≡ cAMP-amplified PKA cascade;
         agent gc ≡ phosphodiesterase-mediated cAMP hydrolysis
```

The 23-row Para-mensch table maps cleanly through ACP — every domain can be mounted as an ACP agent whose tool surface is the substrate-bearer. yb-translator's coalgebra coherence guarantees that re-mounting the same domain over ACP preserves the GF(3) trit.

## Use when

- Picking which ACP client to host an interaction in
- Bridging an ACP session through CapTP (sealed capability piping)
- Locating the local Zig ACP implementation (Zoad)
- Planning Hermes-style "agent-tool-as-sealed-cap" architecture
- Wrapping an existing skill from `repl-commons` or `para-mensch-commons` as an ACP agent

## Related atlases

- **REPL atlas** (runtime): `repl-commons`
- **Para(Optic) atlas** (categorical): `para-mensch-commons`
- **ACP atlas** (protocol): this skill
