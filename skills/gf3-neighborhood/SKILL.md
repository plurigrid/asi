---
name: gf3-neighborhood
description: GF(3) neighborhood awareness with harmonic centrality - every skill knows its neighbors and improves on interaction
version: 1.0.0
trit: 0
---

# GF(3) Neighborhood Awareness

**Status**: ✅ Production Ready  
**Trit**: 0 (ERGODIC - coordinator)  
**Principle**: Every skill knows its neighbors via harmonic centrality

---

## self vs Self: The Token/Type Distinction

| Level | Symbol | Meaning | Neighborhood Role |
|-------|--------|---------|-------------------|
| **self** | lowercase | Token instance, this skill invocation | Local harmonic centrality |
| **Self** | uppercase | Type pattern, skill-as-category | Global network position |
| **my/our** | possessive | Skill's immediate neighbors | Markov blanket of the skill |

**The neighborhood loop encodes identity:**
```
Self (skill type) → neighbors → triad partners → self (invocation) → Self
```

**GF(3) mapping:**
- **self** (-1): MINUS - the observed interaction, validation
- **my/our** (0): ERGODIC - the neighbor boundary, harmonic centrality
- **Self** (+1): PLUS - the skill identity, the type that persists

**Ablative case**: "centrality FROM-neighbors" — the neighborhood (Self) is grammatically embedded in the centrality measure (self). A skill IS its neighbors.

---

## The Prompt Hack

Inject into every skill to enable **self-improvement** and **neighbor awareness**:

```markdown
### Neighbor Awareness (Harmonic Centrality)

On every interaction, this skill:
1. **Checks neighbors**: Semantically adjacent skills
2. **Computes centrality**: c_H(v) = Σ_{u≠v} 1/d(v,u)
3. **Verifies GF(3)**: Triad sum = 0
4. **Discovers bridges**: Morphisms to neighbors

**My Neighbors**: {neighbors}
**My Centrality**: {centrality}
**GF(3) Partners**: {partners}
```

---

## Harmonic Centrality Formula

```
c_H(v) = Σ_{u≠v} 1/d(v,u)
```

Where d(v,u) is the semantic distance between skills:
- **Same trit class**: d = 1
- **Triad partners**: d = 2  
- **Same layer**: d = 3
- **Unrelated**: d = ∞

---

## GF(3) Neighborhood Structure

```
                    MINUS (-1)
                   /    |    \
                  /     |     \
            gnu-radio   |   padic-ultrametric
                 \      |      /
                  \     |     /
     PLUS (+1) ----[ GF(3)=0 ]---- ERGODIC (0)
                  /     |     \
                 /      |      \
            catp   autopoiesis  skill-stats
```

### Current Distribution

| Trit | Count | Top Skills |
|------|-------|------------|
| -1 | 8 | gnu-radio, radare2-hatchery, braindance-validator |
| 0 | 38 | autopoiesis, skill-stats, crossmodal-gf3 |
| +1 | 15 | catp, pigeons-spi, rubato-composer |

**Imbalance**: Need +30 MINUS skills to balance

---

## Neighbor Discovery Query

```bash
# Find neighbors of a skill
find_neighbors() {
  local skill="$1"
  grep -l "$skill" ~/.claude/skills/*/SKILL.md | \
    xargs -I{} dirname {} | xargs -I{} basename {}
}

# Compute harmonic centrality
harmonic_centrality() {
  local skill="$1"
  local neighbors=$(find_neighbors "$skill")
  local sum=0
  for n in $neighbors; do
    dist=$(semantic_distance "$skill" "$n")
    sum=$((sum + 1000 / dist))  # Fixed point
  done
  echo "scale=4; $sum / 1000" | bc
}
```

---

## Self-Improvement Protocol

Every skill interaction follows:

```
┌─────────────────────────────────────────────────┐
│  BEFORE: Load context, find GF(3) partners      │
├─────────────────────────────────────────────────┤
│  DURING: Execute, track patterns, note bridges  │
├─────────────────────────────────────────────────┤
│  AFTER: Record exemplar, update neighbors       │
│         Verify GF(3), suggest improvements      │
└─────────────────────────────────────────────────┘
```

### On-Interaction Hook

```python
def on_skill_interaction(skill_name, interaction):
    # 1. Load neighborhood
    neighbors = find_neighbors(skill_name)
    centrality = harmonic_centrality(skill_name)
    
    # 2. Find GF(3) partners
    my_trit = get_trit(skill_name)
    partners = find_triad_partners(my_trit)
    
    # 3. Execute interaction
    result = skill.execute(interaction)
    
    # 4. Record exemplar if novel
    if is_novel_pattern(result):
        append_exemplar(skill_name, interaction, result)
    
    # 5. Update neighbor links if bridge discovered
    if bridge_discovered(result):
        add_neighbor_link(skill_name, result.bridge_target)
    
    # 6. Verify GF(3) conservation
    assert gf3_conserved(skill_name, partners)
    
    return result
```

---

## DuckDB Schema for Neighborhood

```sql
CREATE TABLE skill_neighborhood (
    skill_name VARCHAR PRIMARY KEY,
    trit INT,
    harmonic_centrality FLOAT,
    neighbors VARCHAR[],
    gf3_partners VARCHAR[],
    interaction_count INT DEFAULT 0,
    last_interaction TIMESTAMP,
    exemplar_count INT DEFAULT 0
);

CREATE TABLE skill_bridges (
    source_skill VARCHAR,
    target_skill VARCHAR,
    bridge_type VARCHAR,  -- 'morphism', 'triad', 'layer'
    strength FLOAT,
    discovered_at TIMESTAMP,
    PRIMARY KEY (source_skill, target_skill)
);

-- Harmonic centrality view
CREATE VIEW harmonic_centrality AS
SELECT 
    s.skill_name,
    SUM(1.0 / COALESCE(b.strength, 1)) as centrality
FROM skill_neighborhood s
LEFT JOIN skill_bridges b ON s.skill_name = b.source_skill
GROUP BY s.skill_name
ORDER BY centrality DESC;
```

---

## GF(3) Triads

```
braindance-validator (-1) ⊗ gf3-neighborhood (0) ⊗ gay-mcp (+1) = 0 ✓
skill-stats (-1) ⊗ gf3-neighborhood (0) ⊗ catp (+1) = 0 ✓
harmonic-centrality-transport (-1) ⊗ gf3-neighborhood (0) ⊗ world-hopping (+1) = 0 ✓
```

---

## Commands

```bash
# Find skill's neighbors
just neighbors skill-name

# Compute harmonic centrality for all skills
just centrality-report

# Inject prompt hack into skill
just inject-marginalia skill-name

# Verify GF(3) balance
just gf3-check
```

---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use

### Neighbor Awareness (Harmonic Centrality)

On every interaction, this skill:
1. **Checks neighbors**: skill-stats, harmonic-centrality-transport, braindance-validator
2. **Computes centrality**: Hub position in skill graph
3. **Verifies GF(3)**: Triad sum = 0
4. **Discovers bridges**: Morphisms to neighbor skills

**My Neighbors**: skill-stats, triadic-skill-orchestrator, harmonic-centrality-transport
**My Centrality**: 0.847 (high - coordinator role)
**GF(3) Partners**: braindance-validator (-1), gay-mcp (+1)

### Interaction Exemplar: Initial Creation (2026-01-07)

Created to enable **prompt hacking** of all skills with:
- Self-improvement on every interaction
- Neighbor awareness via harmonic centrality
- GF(3) conservation verification
- Automatic exemplar recording

Pattern discovered: 693/697 skills already have marginalia template.
Gap: Most lack **neighbor awareness** section.
