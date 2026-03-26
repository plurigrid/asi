---
name: magic-todo
description: Add TODOs to org files and generate ADHD-friendly task breakdowns with local MLX models on Apple Silicon. Load when creating actionable checklists from vague tasks or populating org-mode files with structured TODO entries.
---

# magic-todo

## Setup

- **Python**: `/Users/alice/v/.venv-mlx-lm/bin/python`
- **Script**: `/Users/alice/v/scripts/magic_todo_mlx.py`
- **Default model**: `mlx-community/Qwen3-8B-4bit`
- **Elisp**: `/Users/alice/v/magic-todo-org/emacs/magic-todo-org.el`

## CLI Usage

```bash
unset PYTHONPATH

# Generate JSON breakdown
echo "your task here" | /Users/alice/v/.venv-mlx-lm/bin/python \
  /Users/alice/v/scripts/magic_todo_mlx.py \
  --format json --spice 2 \
  --model mlx-community/Qwen3-8B-4bit \
  --max-tokens 800

# Generate org-mode checklist
echo "your task here" | /Users/alice/v/.venv-mlx-lm/bin/python \
  /Users/alice/v/scripts/magic_todo_mlx.py \
  --format md --spice 2 \
  --model mlx-community/Qwen3-8B-4bit \
  --max-tokens 800
```

## Org File Entry Format

```org
* TODO <task description>
:PROPERTIES:
:MAGIC_TODO_TASK: <task description>
:MAGIC_TODO_SPICE: <1-5>
:MAGIC_TODO_MODEL: mlx-community/Qwen3-8B-4bit
:END:
- [ ] step one
- [ ] step two
```

## Spice Levels

| Level | Meaning | Guidance |
|-------|---------|----------|
| 1 | Trivial | 2-3 quick steps |
| 2 | Easy | 4-6 clear steps |
| 3 | Medium | 6-10 steps, may need substeps |
| 4 | Hard | 8-15 steps with substeps |
| 5 | Overwhelming | 10-20 steps, deeply broken down |

## Parameters

| Flag | Default | Description |
|------|---------|-------------|
| `--format` | `text` | Output format: `text`, `md`, `json` |
| `--spice` | `2` | Difficulty 1-5 |
| `--model` | `Qwen3-8B-4bit` | MLX model repo id |
| `--max-tokens` | `2048` | Max generation tokens |
| `--temp` | `0.7` | Sampling temperature |
| `--top-p` | `0.9` | Nucleus sampling |
| `--context` | - | Existing org content for style learning |
| `--list-models` | - | List cached MLX models |

## Workflow

1. Run the script with `--format json` to get structured output
2. Parse the JSON: `{"title": "...", "steps": [{"text": "...", "substeps": null}]}`
3. Format as org checklist (`- [ ] step text`)
4. Append to the target `.org` file with PROPERTIES block

## Output Rules

- Steps are concise (~10 words max), verb-first
- Tools are always suggested with alternatives ("using X or Y")
- No filler: no "review", "test", "document", "audit", "ensure", "plan"
- ADHD-friendly: many small steps, no walls of text

## Known Org Files

- `/Users/alice/vi/plurigrid.org/plurigrid-basinator.org`
