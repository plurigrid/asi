# vibe-snipe Skill

> *Play/Coplay bidirectional evaluation with compiled artifact verification*

**Trit**: +1 (PLUS - generator)

## Origin

From Interverse transcript (Dec 12, 2025 - Alice Through the Looking Glass):
> "How would you evaluate whether I met your VibeSnipe or not in some artifact that can be verified independently in sort of compiled artifacts of some kind?"

## Core Concept

**VibeSnipe** = Packing context with interleaved structures you already know, then evaluating whether the counterpart met your expectation via compiled artifacts.

```
Player A: Sends VibeSnipe (context-packed prompt)
Player B: Responds with Play
Player A: Evaluates via Coplay (simultaneous with B's evaluation)
Artifact: Compiled verification (Olog, diagram, code)
```

## The Play/Coplay Duality

From open games theory:
```haskell
data OpenGame s t a b = OpenGame
    { play   :: s -> a           -- Forward pass
    , coplay :: (s, b) -> t      -- Backward pass (with context)
    }

-- VibeSnipe is the initial state s
-- Play is the action a
-- Coplay evaluates with access to both s and response b
```

## Artifact Types for Verification

1. **Olog** - Ontology log (categorical diagram)
2. **Colored wiring diagram** - Morphism visualization
3. **Compiled code** - Executable verification
4. **Statement file** - Formal specification

## Implementation

```julia
struct VibeSnipe
    context::Vector{Symbol}       # Interleaved structures
    expectation::Function         # What counts as "met"
    artifact_type::Symbol         # :olog, :wiring, :code
end

struct PlayCoplay
    play::Function                # Player's response
    coplay::Function              # Simultaneous evaluation
end

function evaluate_vibe_snipe(vs::VibeSnipe, pc::PlayCoplay, input)
    play_result = pc.play(input)
    coplay_result = pc.coplay(vs.context, play_result)
    
    # Both evaluate simultaneously - that's the point
    return (
        play_met = vs.expectation(play_result),
        coplay_met = vs.expectation(coplay_result),
        artifact = compile_artifact(vs.artifact_type, play_result)
    )
end
```

## Olog in Lisp

> "Can I make an Olog with this in one? You should be able to... implement the entirety of the Olog in Lisp."

```clojure
;; Olog as S-expression
(defolog alice-chirality
  (objects
    :alice "The English name"
    :elisa "The Spanish name"  
    :chirality "Handedness property")
  (arrows
    [:alice :elisa :via-negativa]
    [:elisa :alice :symmetry-breaking]
    [:chirality :alice :determines]))
```

## Related Skills

- `open-games` (0): Play/Coplay formalism
- `lispsyntax-acset` (+1): Olog in Lisp
- `glass-bead-game` (+1): Interdisciplinary synthesis
- `bisimulation-game` (0): Observational equivalence

## Commands

```bash
# Create VibeSnipe session
bb vibe-snipe.bb --context "chirality,jabberwocky,syntax-physics"

# Compile Olog artifact
just olog-compile alice.olog --format svg
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
