---
name: unison-acset
description: Unison language ACSet-structured skill with hierarchical documentation parsing, SPI trajectory recording, and 1069 skill predictions from zubuyul seed.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Unison ACSet Skill

Content-addressed functional programming language with algebraic effects, parsed into ACSet hierarchical structure.

## Originary Interaction Entropy Seed

**Color World Package**: Identified solely by seed **1069** (0x42D, "zubuyul")

```
Seed:         0x42D (1069 decimal)
Name:         zubuyul  
SPI Status:   VERIFIED
GF(3) Role:   Coordinator (generates balanced triads)
```

## ACSet Schema for Unison Documentation

```
@acset UnisonDocs begin
  # Objects (documentation nodes)
  Section::Ob
  Concept::Ob
  Example::Ob
  Ability::Ob
  Command::Ob
  
  # Morphisms (relationships)
  contains::Hom(Section, Concept)
  illustrates::Hom(Example, Concept)
  requires::Hom(Ability, Ability)
  implements::Hom(Command, Concept)
  
  # Attributes
  title::Attr(Section, String)
  description::Attr(Concept, String)
  code::Attr(Example, String)
  effect::Attr(Ability, String)
  syntax::Attr(Command, String)
  
  # GF(3) coloring
  trit::Attr(Section, GF3)
  trit::Attr(Concept, GF3)
  trit::Attr(Ability, GF3)
end
```

## Hierarchical Documentation Structure

### Level 0: Core Philosophy
| Node | Trit | Description |
|------|------|-------------|
| content-addressed | 0 | Code identified by hash, not name |
| immutability | -1 | Definitions never change once hashed |
| hash-based-deps | +1 | Dependencies pinned by 512-bit SHA3 |

### Level 1: Language Constructs
| Node | Trit | Description |
|------|------|-------------|
| functions | 0 | Pure computations: `f : A -> B` |
| delayed-comps | +1 | Thunks: `'a`, `do`, `_ -> a` |
| types | 0 | Structural vs unique types |
| patterns | -1 | Pattern matching with guards |

### Level 2: Abilities (Effect System)
| Ability | Trit | Handler | Purpose |
|---------|------|---------|---------|
| IO | +1 | Runtime | File, network, console |
| Exception | -1 | `catch`, `toEither` | Error handling |
| Random | 0 | `splitmix seed` | PRNG generation |
| Abort | -1 | `toOptional!` | Early termination |
| Remote | +1 | Cloud ru