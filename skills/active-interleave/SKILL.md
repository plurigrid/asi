# Active Interleave Skill

Interleaves context from recently active Claude/Amp threads into current activity via random walk.

## Activation

Load when context from recent work would help current task.

## Usage

```bash
# Interleave from last 24 hours
bb ~/.claude/skills/active-interleave/active.bb

# Interleave from last N hours
bb ~/.claude/skills/active-interleave/active.bb --hours 6

# Query-focused interleave
bb ~/.claude/skills/active-interleave/active.bb --query "aptos blockchain"

# JSON output
bb ~/.claude/skills/active-interleave/active.bb --json
```

## Behavior

1. **MINUS (-1)**: Validate recency window, filter to active threads only
2. **ERGODIC (0)**: Random walk through recent sessions following awareness edges  
3. **PLUS (+1)**: Emit interleaved fragments with GF(3) coloring

## GF(3) Conservation

Each interleave batch maintains Σ trits ≡ 0 (mod 3).

## Integration

Call from current thread to surface relevant recent context:

```clojure
;; In any bb script
(require '[babashka.process :refer [shell]])
(def context (-> (shell {:out :string} "bb" (str (System/getProperty "user.home") 
                 "/.claude/skills/active-interleave/active.bb") "--json")
                 :out))
```

## Schema

Reads from `~/worldnet/cognition.duckdb`:
- `messages` - Content with timestamps
- `sessions` - Session metadata  
- `awareness_edges` - Play/coplay graph
- `temporal_index` - Time-ordered index
