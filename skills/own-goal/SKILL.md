---
name: own-goal
description: Save session goals to org files in the goals-*.org format. Auto-increments rank, classifies theme, writes org entry with properties and task checklist.
version: 1.0.0
---

# Own Goal

Save the current session's goal to the goals org file at `${GOALS_FILE}`. Each entry gets an auto-incremented rank, a theme classification, TODO state, and a task checklist.

## Usage

When the user says `/own-goal` or asks to "save own goal", do this:

1. Run `scripts/next-rank.sh` to get the next rank number
2. Ask the user for a one-line goal summary (or infer from session context)
3. Classify into a theme from the table below
4. Choose a TODO state: `STARTED`, `IN_PROGRESS`, `SUBSTANTIAL`, `ABANDONED`, or `COMPLETED`
5. Append the org entry to `${GOALS_FILE}` before the `* Cross-References` section

## Theme Classification

Pick the best match. If none fit, use `Miscellaneous`.

| Theme | Tag | Keywords |
|-------|-----|----------|
| Audio & Voice | @audio | audio, voice, recording, whisper, transcribe, mlx, speech, say |
| BCI & Neurotechnology | @bci | bci, eeg, neural, brain, neurofeedback, openbci |
| Biological Time & Body | @bio | circadian, body, sleep, metabolism, lisdexamfetamine, nad |
| Blockchain & Aptos | @chain | aptos, move, nft, mint, wallet, token, blockchain, web3, zora |
| Chromatic Walks & Color | @color | color, gay, chromatic, gf3, trit, splitmix |
| Diagrams & Visualization | @diagrams | diagram, svg, catcolab, olog, graph, mermaid, dot |
| Goals & Planning | @goals | goal, org, plan, regret, rank, session, label |
| Hardware & Device Setup | @hardware | hardware, device, apple watch, sensor, kmonad, xreal |
| Infrastructure & Cloud | @infra | cloudflare, worker, deploy, domain, server, docker, k3s |
| Infrastructure & Trading | @trading | trading, ostium, tenderloin, fund, portfolio, hedge |
| LoLa Pipeline | @lola | lola, lolita, physics, emulation, latent |
| Miscellaneous | @misc | (fallback) |
| Networking & Connectivity | @network | tailscale, ssh, vpn, localsend, p2p, iroh |
| Perceivable & Worldmodel | @world | world, perceivable, active inference, free energy |
| Regret & History | @regret | regret, history, duckdb, session, pipeline |
| Research & Repos | @research | paper, arxiv, research, repo, clone, github |
| Scrivener & Writing | @writing | scrivener, writing, novel, manuscript, sun |
| Skills & Meta | @skills | skill, meta, droid, mcp, plugin, hook |
| Social Graph & Messaging | @social | beeper, signal, message, chat, social, group |
| Subagent & Workers | @workers | subagent, worker, swarm, parallel, dispatch |
| System & Process Mgmt | @system | process, cron, daemon, launchd, macos, system |
| Video & Phone | @video | video, phone, camera, screen, recording |
| World Loom & Trust Games | @trust | trust, game, arena, challenge, loom, worldline |

## Org Entry Template

```org
** STATE #RANK: SUMMARY
:PROPERTIES:
:SESSION_ID: SESSION_ID_OR_DATE
:SOURCE:     SOURCE
:RANK:       RANK
:THEME:      THEME_NAME
:TAG:        @TAG
:START:      [YYYY-MM-DD DAY]
:END:

*** Context
- Brief context line 1
- Brief context line 2

*** Tasks
- [ ] Task 1
- [ ] Task 2
```

### Fields

- **STATE**: One of `STARTED`, `IN_PROGRESS`, `SUBSTANTIAL`, `ABANDONED`, `COMPLETED`
- **RANK**: Auto-incremented via `scripts/next-rank.sh`
- **SUMMARY**: First 120 chars of goal description
- **SESSION_ID**: From `.claude/history.jsonl` or `.factory/history.json`, or `session-YYYY-MM-DD` if manual
- **SOURCE**: `claude`, `factory`, or `conversation`
- **START**: Today's date in org timestamp format `[YYYY-MM-DD DAY]`

## Placement

Append the new entry inside the matching `* THEME (N)` section if it exists. If the theme section doesn't exist yet, create it before `* Cross-References`. Update the count in the theme heading.

## Target File

Auto-discovered: the script finds the newest `goals-*.org` in `~/worlds/`, `~/v/`, or `.`.
