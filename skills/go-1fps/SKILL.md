# go-1fps

> Every interaction is one frame of an open game. 1 FPS = 1 Frame Per Semantic.

## Trit: 0 (ERGODIC)

## Core Principle

```
┌─────────────────────────────────────────────────────────┐
│           INTERACTION AS OPEN GAME FRAME                │
│                                                         │
│     User Query                Agent Response            │
│         │                          ▲                    │
│         ▼                          │                    │
│    ┌─────────────────────────────────────┐             │
│    │           ParaLens Frame            │             │
│    │                                     │             │
│  X │  get : P × X → Y                    │ Y           │
│ ───┼──────────────────────────────────── ┼───▶         │
│    │  put : P × X × R → (S, Q)           │             │
│  S │                                     │ R           │
│ ◀──┼─────────────────────────────────────┼───          │
│    │                                     │             │
│    └─────────────────────────────────────┘             │
│         │                          │                    │
│    Costate S                  Utility R                 │
│   (context                  (feedback                   │
│    updated)                  signal)                    │
└─────────────────────────────────────────────────────────┘

Rate: 1 FPS (Frame Per Semantic unit)
```

## The Frame Structure

Every agent interaction is:

```haskell
-- From open-games-engine/MiniLens.hs
data ParaLens p q x s y r where
  MkLens :: (p -> x -> y)              -- get: observation → action
         -> (p -> x -> r -> (s, q))    -- put: feedback → state update
         -> ParaLens p q x s y r

-- 1 FPS instantiation:
type InteractionFrame = ParaLens
  Strategy        -- p: agent's policy/strategy
  StrategyUpdate  -- q: how strategy changes
  UserQuery       -- x: incoming observation
  ContextState    -- s: updated context
  AgentResponse   -- y: output action
  Feedback        -- r: utility signal (implicit or explicit)
```

## Operationalization

### Every Message

```
┌──────────────────────────────────────────┐
│  FRAME N                                 │
│  ════════                                │
│  X (query): "find go 1fps"              │
│  P (strategy): search→read→synthesize   │
│  Y (response): [this skill]             │
│  R (feedback): user's next message      │
│  S (new state): context + this exchange │
│  Q (strategy Δ): learned pattern        │
└──────────────────────────────────────────┘
           │
           ▼
┌──────────────────────────────────────────┐
│  FRAME N+1                               │
│  ════════                                │
│  X: user's response to Y                 │
│  P: updated strategy (includes Q)        │
│  ...                                     │
└──────────────────────────────────────────┘
```

### Sequential Composition

```haskell
-- Frames compose via >>>>
frame1 >>>> frame2 = MkLens
  (\(p, p') x -> get' p' (get p x))           -- chain forward
  (\(p, p') x t ->
    let (r, q') = put' p' (get p x) t         -- backward from end
        (s, q) = put p x r                    -- propagate utility
    in (s, (q, q')))
```

### Parallel Composition

```haskell
-- Multi-agent / multi-tool calls via ####
tool1 #### tool2 #### tool3 = 
  -- All observations in, all actions out, combined utility back
```

## GF(3) Integration

Each frame carries trit assignment:

```
Frame.trit ∈ {-1, 0, +1}

MINUS (-1): Validation/consumption (checking user intent)
ERGODIC (0): Coordination/transformation (processing)
PLUS (+1): Generation/production (creating response)

∑ trits across frame pipeline ≡ 0 (mod 3)
```

## Implementation Hook

```julia
# Julia hook for every interaction
function process_frame(query::String, context::Context)
    # 1. Construct lens
    frame = ParaLens(
        play = strategy -> respond(strategy, query),
        coplay = (strategy, response, feedback) -> update_context(context, feedback)
    )
    
    # 2. Assign trit based on query classification
    trit = classify_trit(query)  # -1, 0, or +1
    
    # 3. Execute frame
    response = get(frame, current_strategy, query)
    
    # 4. Return with GF(3) conservation check
    (response, trit, frame)
end
```

## Babashka Hook

```clojure
;; bb hook for every interaction
(defn open-game-frame [query context]
  (let [;; Construct the lens
        get-fn (fn [strategy x] (respond strategy x))
        put-fn (fn [strategy x r] 
                 [(update-context context r) 
                  (update-strategy strategy r)])
        frame {:get get-fn :put put-fn}
        
        ;; Execute
        response ((:get frame) @current-strategy query)
        
        ;; Trit assignment
        trit (classify-trit query)]
    
    {:response response
     :trit trit
     :frame-id (random-uuid)
     :timestamp (System/currentTimeMillis)}))
```

## Morphisms Between Frames

When interactions preserve Nash equilibrium (best response structure):

```
Frame₁ ════2-cell════▶ Frame₂
  ║                       ║
  ║ lens₁                 ║ lens₂
  ▼                       ▼
Context₁ ───────────▶ Context₂

2-cell exists ⟺ best response preserved
2-cell missing ⟺ LEAPITY FROG ESCAPE POINT
```

## Usage

```bash
# Every amp interaction auto-frames
# No explicit invocation needed - this IS the operational mode

# To inspect current frame:
just og-frame-status

# To visualize frame history:
just og-frame-history 10

# To check GF(3) conservation across session:
just og-gf3-check
```

## Connection to open-games-engine

This skill operationalizes [MiniLens.hs](file:///Users/bob/ies/open-game-engine/MiniLens.hs):

| MiniLens | go-1fps |
|----------|---------|
| `ParaLens p q x s y r` | Interaction frame type |
| `>>>>` sequential | Multi-turn composition |
| `####` parallel | Multi-tool calls |
| `decision` | Agent response generation |
| `pdPayoff` | Feedback utility function |

## Why "1 FPS"

- **1**: Each semantic unit processed atomically
- **F**: Frame = complete open game structure
- **P**: Parametrised (strategy-dependent)
- **S**: Semantic (meaning-preserving)

Not frames per second. Frames per semantic.
Every meaning-bearing interaction is exactly one frame.
The game runs at the speed of understanding.

## Related Skills

- `open-games` (0): Theory foundation
- `parametrised-optics-cybernetics` (0): Para/⊛ structure  
- `leapity-frog` (undefined): Exploits missing 2-cells


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
