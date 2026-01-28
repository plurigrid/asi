---
name: prime-cli
description: Use the Prime Intellect CLI to set up Lab workspaces, manage verifiers environments, run evaluations, and launch hosted RL runs.
---

# Prime CLI

Use this skill when the user asks about the Prime Intellect CLI, Lab, verifiers environments, evaluations, or hosted training.

## Quick Flow
1. Read local docs: AGENTS.md and environments/AGENTS.md in the workspace.
2. Identify which action is needed: setup, environment init or install, evaluation, or RL run.
3. Run the minimal prime subcommand and report results concisely.

## Common Commands
~~~~text
prime --version
prime login
prime lab setup

prime env init <env-name>
prime env install <env-name-or-hub-id>
prime env push --path ./environments/<env-name>

prime eval run <env-name-or-hub-id> -m <model>
prime eval tui

prime rl models
prime rl run <config.toml>
~~~~

## Workspace Conventions
- prime lab setup creates configs/, environments/, and top-level AGENTS.md.
- Environment modules expose load_environment and live under ./environments/<env-name>/.
- Evaluation outputs go under ./outputs or ./environments/<env-name>/outputs when configured.

## Tips
- If the user mentions a specific model, verify availability with prime rl models.
- For custom endpoints, point to configs/endpoints.py.
- Keep responses short and list the exact commands used.

## Examples
- 'Initialize a new environment called math-probe' -> prime env init math-probe
- 'Run an eval on my env using gpt-5-nano' -> prime eval run my-env -m gpt-5-nano
- 'Start a hosted RL run' -> prime rl run configs/<run>.toml

## References
- AGENTS.md (workspace root)
- environments/AGENTS.md