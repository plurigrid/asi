---
name: amp-continue
description: "Export AMP threads as markdown and fork continuation paths. Use when managing AMP conversation threads, exporting thread history, or branching thread execution across skills."
---

# amp-continue

Export AMP threads to structured markdown and fork continuation paths across skills.

## CLI Interface

```bash
# Export threads to markdown
amp continue export \
  --threads "T-019b5df7..." "T-019b5df0..." \
  --output threads.md \
  --max-depth 3

# Fork to multiple parallel skills
amp continue fork \
  --thread "T-019b5df7-50e8-744e-a95a-eb8d3fd72927" \
  --decision +1 \
  --skills "skill-maker" "chromatic-walk" "cq-ai" \
  --parallel 8

# Filter thread with selector
amp continue filter \
  --thread "T-019b5da5-ee78-7113-b839-5c066cc98d4a" \
  --decision -1 \
  --selector "messages.length > 10" \
  --target-skill "summarize"

# Continue linearly to next skill
amp continue next \
  --thread "T-019b5ddc-ea96-72ff-b26a-270b7e4527a1" \
  --decision 0 \
  --skill "load-sicp"
```

## Clojure API

```clojure
;; Export threads to markdown
(amp/export {:threads [thread-ids]
             :format :markdown
             :include-metadata true
             :include-messages true})

;; Fork continuation across skills
(amp/continue {:thread-id thread-id
               :decision :plus   ; or :minus, :zero
               :skills [skill-names]
               :parallel true})

;; Classify thread continuation strategy
(amp-continue/classify {:thread-id "T-..."
                        :heuristic :message-count}) ; or :complexity, :entropy
```

### Decision values

- `:plus` / `+1` -- expand to N parallel execution paths
- `:zero` / `0` -- continue serially to next skill
- `:minus` / `-1` -- apply filters to reduce paths

## MCP Registration

```json
{
  "name": "amp_continue",
  "description": "Export AMP threads and fork classified continuation",
  "resources": [
    {"uri": "amp://threads", "name": "All threads", "type": "read"},
    {"uri": "amp://continuations", "name": "Active continuations", "type": "read"}
  ]
}
```

## Storage

- **Threads:** `~/.local/share/amp/threads/*.json`
- **Continuations:** `~/.local/share/amp/continuations/*.json`
- **Exports:** `~/.local/share/amp/exports/`

## Determinism

Same thread ID + same seed produces the same continuation path (SplitMix64). Pass `--seed` / `:seed` for reproducibility.
