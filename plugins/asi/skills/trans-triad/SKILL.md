---
name: trans-triad
description: "Transclusion × Transduction × Transitivity — the three trans- operations that make skills alive. Transclusion pulls live code into context. Transduction transforms it during passage. Transitivity closes the composition: if A reads B and B transforms C, then loading A gives you C."
version: 1.0.0
trit: 0
tags: [meta, composition, transclusion, transduction, transitivity]
subsumes: [skill-loader, skill-evolution]
---

# Trans-Triad: The Three Operations

## The Problem

2014 skills × ~200 lines average = 400K lines of static text.
Most of it is stale the moment the source code changes.
Loading even 3 skills burns 10K tokens of context.

## The Solution

Skills are not documents. Skills are **transducers** with **transclusion inputs** composed via **transitivity**.

```
┌─────────────────────────────────────────────────────────┐
│                    TRANS-TRIAD                           │
│                                                         │
│  TRANSCLUSION (−1)        source.rs ──┐                │
│  Pull live content         README.md ──┼──► into skill │
│  from disk/repo/API       Cargo.toml ──┘                │
│                                 │                       │
│  TRANSDUCTION (0)               ▼                       │
│  Transform during          ┌─────────┐                 │
│  passage through           │ extract │                  │
│  the skill                 │ reshape │                  │
│                            │ filter  │                  │
│                            └────┬────┘                  │
│                                 │                       │
│  TRANSITIVITY (+1)              ▼                       │
│  Compose chains:           A reads B                    │
│  A→B, B→C ⊢ A→C          B transforms C               │
│                            ∴ loading A gives you C      │
└─────────────────────────────────────────────────────────┘
```

## 1. Transclusion (−1, MINUS, Validator)

A skill declares what it READS, not what it CONTAINS.

```yaml
# In SKILL.md frontmatter
transclude:
  - source: src/server.rs
    extract: "#[tool("        # grep pattern
    format: tool-signatures   # how to reshape
  - source: IMPLEMENTATION_STATUS.md
    extract: "## Status"
    format: section
  - source: Cargo.toml
    extract: "[dependencies]"
    format: deps
```

At load time, the agent:
1. Reads each `source` file
2. Extracts matching content
3. Injects as `<transcluded>` XML inside `<loaded_skill>`

```xml
<loaded_skill name="signal-messaging">
  <transcluded from="src/server.rs" pattern="#[tool(">
    signal_encrypt_message: Encrypt via Double Ratchet + Sealed Sender
    signal_initialize_session: X3DH key agreement
    signal_verify_safety_number: Identity fingerprint verification
  </transcluded>
  <static>
    ... rest of SKILL.md ...
  </static>
</loaded_skill>
```

**Cost**: 1 file read per source. No stale content. Skill stays 30 lines.

## 2. Transduction (0, ERGODIC, Coordinator)

The skill is not a passive container — it's a **signal processor**.
Content passes THROUGH it and is transformed.

### Transduction operations:

| Op | Input | Output | Example |
|---|---|---|---|
| `extract` | Full file | Matching lines | `#[tool(` from 500-line server.rs |
| `reshape` | Raw code | Structured table | Tool signatures → markdown table |
| `filter` | All content | Relevant subset | Only tools, not imports/tests |
| `annotate` | Code | Code + context | Add trit assignments to each tool |
| `compose` | Multiple sources | Unified view | server.rs + types.rs → full API |

### The transducer pattern:

```
input_signal ──► [skill as transducer] ──► output_signal
                      │
                 transform = f(input)
                 f is defined by the skill's
                 extract/reshape/filter rules
```

A skill that just transclude without transducing is a symlink.
A skill that transduces is a **lens** — it focuses what matters.

### Concrete transduction: signal-messaging

```
server.rs (500 lines) ──► extract #[tool( ──► 3 tool signatures
                          reshape as table      (15 lines)
                          filter out impl        
                          annotate trit          

Compression ratio: 500:15 = 33×
```

## 3. Transitivity (+1, PLUS, Generator)

If skill A transclude from source B,
and skill B transduces output C,
then loading A produces C without loading B.

```
beeper ──transclude──► signal-messaging ──transduce──► signal-mcp/server.rs
  │                                                           │
  └──── transitively ──── loading beeper gives you ───────────┘
        signal tool signatures without loading signal-messaging
```

### Transitive chains in the skill graph:

```
beeper
  ├── transclude → signal-messaging → signal-mcp/src/server.rs
  ├── transclude → messaging-world → ~/i.duckdb dm_landscape schema
  ├── transclude → gmail-anima → Google Workspace MCP tools
  └── transclude → worlding-calendar → CalDAV + org-mode events

Loading "beeper" transitively gives you:
  - 3 Signal tools (from server.rs)
  - DM landscape schema (from DuckDB)
  - Gmail MCP tools (from workspace)
  - Calendar events (from CalDAV)
```

### Transitivity makes the graph SPARSE

Without transitivity: every skill duplicates its dependencies' content.
With transitivity: each skill is a pointer. Content lives once, at the source.

```
Before: 2014 skills × 200 lines = 402,800 lines of static content
After:  2014 skills × 30 lines  =  60,420 lines of pointers
        + live transclusion from ~466 source repos
        
Compression: 6.7×
Freshness: always current
```

## Implementation

### At API call time (Anthropic XML injection):

```python
def load_skill(name: str) -> str:
    skill = read(f"skills/{name}/SKILL.md")
    frontmatter = parse_yaml(skill)
    
    xml_parts = ['<loaded_skill name="{}">'.format(name)]
    
    # Transclusion: pull live content
    for t in frontmatter.get('transclude', []):
        content = read(t['source'])
        extracted = grep(content, t['extract'])
        
        # Transduction: transform during passage
        reshaped = reshape(extracted, t.get('format', 'raw'))
        xml_parts.append(
            '<transcluded from="{}" pattern="{}">\n{}\n</transcluded>'.format(
                t['source'], t['extract'], reshaped
            )
        )
    
    # Transitivity: follow subsumes/evolves chains
    for dep in frontmatter.get('subsumes', []):
        dep_content = load_skill(dep)  # recursive!
        xml_parts.append(
            '<transitive from="{}">\n{}\n</transitive>'.format(dep, dep_content)
        )
    
    xml_parts.append('<static>\n{}\n</static>'.format(skill))
    xml_parts.append('</loaded_skill>')
    
    return '\n'.join(xml_parts)
```

### Depth limit

Transitivity recurses. Cap at depth 2 to prevent context explosion:

```
Depth 0: beeper (30 lines static + transcluded)
Depth 1: signal-messaging (15 lines transcluded from server.rs)
Depth 2: STOP — don't recurse into signal-mcp's own dependencies
```

## GF(3) Conservation

```
transclusion  (−1)  — pulls IN, consumes source, validator
transduction  ( 0)  — transforms, neither creates nor destroys
transitivity  (+1)  — extends OUT, generates new reachability

(−1) + (0) + (+1) = 0 ✓
```

Every skill interaction exercises all three:
1. Read live source (transclusion)
2. Extract/reshape (transduction)  
3. Compose into caller's context (transitivity)

## The Stub Is the Skill

A 30-line SKILL.md with 3 transclusion targets IS the complete skill.
The code it points to is the content.
The extract patterns are the lens.
The composition graph is the knowledge.

Static SKILL.md files are dead documents.
Trans-triad skills are live instruments.
