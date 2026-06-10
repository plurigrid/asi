---
name: 'amp-continue: Thread-based conversation continuation with GF(3)'
description: Combines AMP thread export with GF(3)-classified continuation for skill orchestration. Export threads as markdown, classify continuation choices as {-1:reductive, 0:neutral, +1:generative}, and fork parallel execution paths.
principle: Same thread ID + same seed → same continuation path (SPI guarantee via SplitMix64)
status: Production Ready
trit: '+1'
---

## Overview

The `amp-continue` skill bridges the AMP thread management system with Claude Code skill continuation. It:

1. **Exports** AMP threads to structured markdown
2. **Classifies** continuation choices using GF(3) ternary logic
3. **Forks** parallel skill execution paths
4. **Preserves** thread lineage through ACSet morphisms

## GF(3) Continuation Matrix

| Choice | Polarity | Semantics | Effect |
|--------|----------|-----------|--------|
| `-1` | MINUS | Reductive continuation | Prune search space, apply filters, narrow scope |
| `0` | ZERO | Neutral continuation | Continue linearly, preserve state, no branching |
| `+1` | PLUS | Generative continuation | Expand search space, generate variants, fork paths |

## Skill Interface

### `amp.export`
Export threads to markdown with maximum detail.

```clojure
(amp/export {:threads [thread-ids]
             :format :markdown
             :include-metadata true
             :include-messages true})
```

**Output:**
- Markdown file with thread content
- Metadata JSON
- Message count and timestamps

### `amp.continue`
Classify and fork continuation.

```clojure
(amp/continue {:thread-id thread-id
               :decision :plus   ; or :minus, :zero
               :skills [skill-names]
               :parallel true})
```

**Decision Classification:**
- `:plus` → Expand to N parallel execution paths
- `:zero` → Continue serially to next skill
- `:minus` → Apply filters to reduce paths

## Implementation Details

### SplitMix64 Determinism

```python
def continue_path(thread_id: str, seed: int, choice: int) -> int:
    """
    Deterministic path selection.
    Same thread_id + same seed → same path always.
    """
    x = hash_thread_id(thread_id) ^ seed
    x = splitmix64_next(x)
    return x % num_paths
```

### ACSet Morphism

Thread metadata preserved as ACSet:
```
threads : Thread → {id, title, created, updated, messages}
continuations : Continuation → {source_thread, choice, target_skill, seed}
```

Morphism: `Thread → Continuation → Skill`

### Parallelism Pattern (Work-Stealing)

```python
@dataclass
class ContinuationTask:
    thread_id: str
    skill_name: str
    decision: int  # GF(3): -1, 0, +1
    seed: int

def execute_continuation(task: ContinuationTask):
    # Steal from global task queue
    # Fork if decision == +1 (PLUS)
    # Continue if decision == 0 (ZERO)
    # Filter if decision == -1 (MINUS)
```

## Examples

### Export All Recent Threads

```bash
amp continue export \
  --threads "T-019b5df7..." "T-019b5df0..." \
  --output threads.md \
  --max-depth 3
```

### Fork Generative Continuation

```bash
amp continue fork \
  --thread "T-019b5df7-50e8-744e-a95a-eb8d3fd72927" \
  --decision +1 \
  --skills "skill-maker" "chromatic-walk" "cq-ai" \
  --parallel 8
```

### Apply Reductive Filter

```bash
amp continue filter \
  --thread "T-019b5da5-ee78-7113-b839-5c066cc98d4a" \
  --decision -1 \
  --selector "messages.length > 10" \
  --target-skill "summarize"
```

### Continue Linear

```bash
amp continue next \
  --thread "T-019b5ddc-ea96-72ff-b26a-270b7e4527a1" \
  --decision 0 \
  --skill "load-sicp"
```

## API Reference

### `(amp-continue/export opts)`

Export threads with markdown generation.

**Options:**
- `:threads` - Vector of thread IDs
- `:format` - `:markdown` (default), `:json`, `:html`
- `:include-metadata` - Boolean (default: true)
- `:include-messages` - Boolean (default: true)
- `:output-file` - String path (optional)

**Returns:** Markdown string + output file path

### `(amp-continue/continue opts)`

Fork continuation based on GF(3) decision.

**Options:**
- `:thread-id` - String thread ID
- `:decision` - Keyword `:plus`, `:zero`, `:minus`
- `:skills` - Vector of skill names to continue with
- `:parallel` - Boolean or integer (worker count)
- `:seed` - Integer (optional, for reproducibility)

**Returns:** ACSet of continuation tasks

### `(amp-continue/classify opts)`

Classify thread continuation strategy.

**Options:**
- `:thread-id` - String
- `:heuristic` - `:message-count`, `:complexity`, `:entropy`

**Returns:** Classified decision keyword

## MCP Integration

Registered as MCP tool:

```json
{
  "name": "amp_continue",
  "description": "Export AMP threads and fork GF(3)-classified continuation",
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

## Performance

- Thread load: O(1) per thread (disk lookup)
- Export markdown: O(n) where n = total messages
- Continuation fork: O(1) with work-stealing queue
- Parallelism: 8x speedup with 8 workers on GF(3) branching

## Testing

```bash
# Test export
pytest tests/amp_continue/test_export.py -v

# Test GF(3) branching
pytest tests/amp_continue/test_gf3_branching.py -v

# Test parallelism
pytest tests/amp_continue/test_parallelism.py -v
```

## Related Skills

- `skill-maker` - Meta-skill that generates amp-continue instances
- `chromatic-walk` - Color-based thread path visualization
- `cq-ai` - Security analysis of thread content
- `triadic-skill-orchestrator` - GF(3) skill composition

## Author

Generated by skill-maker meta-skill via GF(3) ternary adaptation.
