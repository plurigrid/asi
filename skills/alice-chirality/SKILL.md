# alice-chirality Skill

> *Helicity vs Chirality koan + Jabberwocky syntax-physics + bilingual symmetry breaking*

**Trit**: 0 (ERGODIC - bridge)

## Origin

From Interverse transcript (Dec 12, 2025):
> "My cat's name is Alice Through the Looking Glass... The difference between helicity and chirality is one is massless. No, no, that's a question you're supposed to answer. A koan usually has the answer."

## The Koan

**Q: What is the difference between helicity and chirality?**

**A: Chirality is Lorentz-invariant (intrinsic handedness). Helicity is frame-dependent (spin projection on momentum). For massless particles, they coincide. For massive particles, helicity can flip under Lorentz boosts, but chirality cannot.**

```
MASSLESS: helicity = chirality (locked)
MASSIVE:  helicity ≠ chirality (can differ by frame)
```

## Enantiomeric Reflection

Alice Through the Looking Glass = reflection on:
- **Enantiomers**: Mirror-image molecules (same atoms, different handedness)
- **Chirality**: The property of non-superimposability
- **Multiscale phenomenon**: From proteins to particle physics

```
Left hand ≢ Right hand
L-amino acids ≢ D-amino acids  
Alice ≢ Elisa (symmetry-broken by language)
```

## Jabberwocky: Syntax-Physics

> "The information you are gleaning is information you are getting from the grammar of the sentence. You don't actually need the words."

```
'Twas brillig, and the slithy toves
Did gyre and gimble in the wabe
```

You understand:
- "brillig" = adjective describing time/state
- "slithy" = adjective (slippery + lithe?)
- "toves" = plural noun (creatures)
- "gyre" = verb (to move)

**Syntax carries meaning without semantics.** This is what DisCoPy and categorical grammar formalize.

## Bilingual Symmetry Breaking

```
Elisa (Spanish) ↔ Alice (English)

The full name: "Alice Through the Looking Glass"
- Handed: two elements of the same work
- Via negativa: infer one from absence of other
- Less is more: "Elisa" implies "Alice" to English speakers
```

## GF(3) Chirality Mapping

```julia
function chirality_trit(handedness::Symbol)
    handedness == :left  && return -1  # MINUS
    handedness == :right && return +1  # PLUS
    handedness == :achiral && return 0 # ERGODIC
end

# Conservation: L + R = 0 (mod 3) for enantiomeric pair
# But: L + L + R = 0 (mod 3) also works!
```

## Related Skills

- `possible_girls` (+1): Tonnetz chirality in music
- `topos-of-music` (+1): PLR group as handedness
- `discopy` (0): Categorical grammar
- `reversible-computing` (-1): Time-symmetric (achiral) computation

## The Play

When introducing the cat:
- To English friends: "Alice"
- To Spanish friends: "Elisa"
- Full name breaks symmetry: "Alice a través del espejo"

## Commands

```bash
# Test chirality koan
julia --project=. -e 'using Gay; chirality_koan_test()'

# Generate enantiomeric color pair
just enantiomer-colors seed=1069
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
