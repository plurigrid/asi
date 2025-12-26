# Copy-on-Interact: Bidirectional GitHub ↔ ACSet Sync

**Seed**: 0x42D | **GF(3) Status**: CONSERVED

## Overview

Copy-on-interact materializes remote state **lazily** on first cross-boundary access:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        COPY-ON-INTERACT ARCHITECTURE                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   Local ACSet                          GitHub Universe                       │
│   ┌──────────────┐                    ┌──────────────────────────────────┐  │
│   │   Thread A   │──on_interact()────►│  bmorphism/Gay.jl (fork)         │  │
│   │   Thread B   │◄──materialize()────│  AlgebraicJulia/Catlab.jl (PR)   │  │
│   │   Thread C   │                    │  ToposInstitute/poly (star)      │  │
│   └──────────────┘                    └──────────────────────────────────┘  │
│         │                                          │                         │
│         └────────────bidirectional─────────────────┘                         │
│                           │                                                  │
│                    ┌──────▼──────┐                                          │
│                    │ Interaction │                                          │
│                    │     Log     │                                          │
│                    │  + Colors   │                                          │
│                    │  + Trits    │                                          │
│                    └─────────────┘                                          │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Interaction Types → GF(3) Trits

| Type | Trit | Hue | Semantic |
|------|------|-----|----------|
| `fork` | ⊖ (-1) | 270° Purple | Constraint: derivation from source |
| `pr` | ⊕ (+1) | 60° Orange | Generation: contribution back |
| `issue` | ○ (0) | 180° Cyan | Coordination: problem tracking |
| `mention` | ○ (0) | 200° Blue | Coordination: reference |
| `star` | ⊕ (+1) | 45° Gold | Generation: appreciation |
| `review` | ⊖ (-1) | 290° Purple | Constraint: validation |

## Usage

### Julia

```julia
using .CopyOnInteract

state = create_state(0x42D)

# Interact with GitHub
on_interact!(state, "https://github.com/AlgebraicJulia/Catlab.jl", :fork)
on_interact!(state, "https://github.com/bmorphism/Gay.jl/pull/3", :pr)

# Create bidirectional thread link
create_bidirectional_link!(state, thread_a, thread_b)

# Verify conservation
@assert verify_gf3_conservation(state)
```

### Python

```python
from lib.copy_on_interact import CopyOnInteractState, InteractionType

state = CopyOnInteractState(seed=0x42D)

# Interact with GitHub
state.on_interact("https://github.com/AlgebraicJulia/Catlab.jl", InteractionType.FORK)
state.on_interact("https://github.com/bmorphism/Gay.jl/pull/3", InteractionType.PR)

# Bidirectional thread links
fwd, bwd = state.create_bidirectional_link("T-001", "T-002")

# Verify conservation
assert state.verify_gf3_conservation()
```

### CLI via gh

```bash
# Fetch interaction data
gh api repos/AlgebraicJulia/Catlab.jl --jq '{stars: .stargazers_count, forks: .forks_count}'

# List contributors (cobordism detection)
gh api repos/AlgebraicJulia/Catlab.jl/contributors --jq '.[].login'

# Find cross-repo patterns
comm -12 <(gh api repos/AlgebraicJulia/Catlab.jl/contributors --jq '.[].login' | sort) \
         <(gh api repos/ToposInstitute/poly/contributors --jq '.[].login' | sort)
```

## ACSet Schema

```
@present SchInteractiveACSet(FreeSchema) begin
    Thread::Ob
    Skill::Ob
    Agent::Ob
    RemoteRef::Ob
    Interaction::Ob
    
    references::Hom(Thread, Thread)        # Bidirectional links
    remote_source::Hom(RemoteRef, Thread)  # GitHub → local
    
    interaction_type::Attr(Interaction, InteractionType)
    color::Attr(Interaction, OkLCH)
    trit::Attr(Interaction, GF3)
end
```

## Cobordism Detection

Find shared boundaries between repo communities:

```python
cobordisms = state.find_cobordisms()
# Returns: [
#   {"repos": ("Catlab.jl", "poly"), "shared_count": 3, "net_trit": 0},
#   {"repos": ("Gay.jl", "ACSets.jl"), "shared_count": 1, "net_trit": 1},
# ]
```

Key bridge authors (from gh-interactome skill):
- `olynch`: ToposInstitute ↔ AlgebraicJulia
- `epatters`: Catlab ↔ ACSets ↔ Topos
- `abooij`: HoTT ↔ Cubical

## GF(3) Conservation

Every balanced interaction triad:
```
fork(-1) + issue(0) + pr(+1) = 0 ✓
```

## Files

| File | Language | Purpose |
|------|----------|---------|
| [lib/copy_on_interact.jl](lib/copy_on_interact.jl) | Julia | ACSet integration |
| [lib/copy_on_interact.py](lib/copy_on_interact.py) | Python | gh CLI bridge |
| [gh_acset_export.json](gh_acset_export.json) | JSON | Export schema |

## Integration with Existing Skills

- **gay-mcp**: Deterministic color generation for interactions
- **acsets**: Schema and DPO merge semantics
- **gh-interactome**: Contributor network discovery
- **bisimulation-game**: Verify thread equivalence
- **world-hopping**: Navigate between repo-worlds

## Live Thread Attachments

Conversations that evolve over time map to:
1. **Thread** - conversation context
2. **Interactions** - events (messages, tool calls)
3. **RemoteRefs** - external resources fetched
4. **Cobordisms** - cross-thread/cross-repo patterns

```python
# Attach live process to thread
state.on_interact(
    f"amp://threads/{thread_id}",
    InteractionType.THREAD_REF
)
```
