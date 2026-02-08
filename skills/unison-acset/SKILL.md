# unison-acset

ACSet-structured Unison documentation with SPI trajectory recording.

## Overview

Parses Unison language documentation into ACSet schema for structured navigation, with deterministic color world package generation.

**Origin**: PR #36 (closed, consolidated into main via #42)
**Seed**: 1069 (0x42D, "zubuyul")

## ACSet Schema

```julia
@present SchUnisonDoc(FreeSchema) begin
    Section::Ob
    Concept::Ob
    Ability::Ob
    Example::Ob
    
    section_concept::Hom(Concept, Section)
    concept_ability::Hom(Ability, Concept)
    ability_example::Hom(Example, Ability)
    
    name::Attr(Section, String)
    code::Attr(Example, String)
    hash::Attr(Concept, UInt64)  # Content-addressed
end
```

## Color World Package

A package identified **only by its originary interaction entropy seed color**:

```
Seed:     1069 (0x42D)
Identity: SHA3-512(seed)
Name:     (none - the color sequence IS the identity)
```

## SPI Trajectory Recorder

```clojure
#!/usr/bin/env bb
;; spi_trajectory.bb - Record color trajectory from seed

(def GOLDEN 0x9e3779b97f4a7c15)
(def MIX1 0xbf58476d1ce4e5b9)
(def MIX2 0x94d049bb133111eb)

(defn splitmix64 [x]
  (let [z (unchecked-add x GOLDEN)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) MIX1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) MIX2)]
    (bit-xor z (unsigned-bit-shift-right z 31))))

(defn trajectory [seed n]
  (take n (iterate splitmix64 (splitmix64 seed))))
```

## 1069 Skill Predictions

Using seed 1069, predict trit distribution over 1069 skills:

| Trit | Role | Expected % |
|------|------|------------|
| +1 | PLUS (generative) | ~25% |
| 0 | ERGODIC (coordination) | ~30% |
| -1 | MINUS (validation) | ~45% |

## GF(3) Trit

**Trit: 0** (ERGODIC) - Schema coordination

## Related Skills

- `acsets-algebraic-databases` - ACSet foundations
- `unison` - Unison language
- `splitmix-ternary` - Ternary RNG
