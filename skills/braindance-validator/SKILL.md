---
name: braindance-validator
description: Validates GF(3) conservation across triadic braindance replays. Ensures MINUS+ERGODIC+PLUS=0.
version: 1.0.0
trit: -1
---

# Braindance Validator

**Status**: ✅ Production Ready  
**Trit**: -1 (MINUS - validation/verification)  
**Purpose**: Verify GF(3) conservation across parallel agent braindances

---

## Validation Rules

### 1. Triadic Conservation
Every braindance must satisfy:
```
Σ(agent_trits) ≡ 0 (mod 3)
```

### 2. Sonification Correspondence
| Trit | Waveform | Frequency Range | Hue Range |
|------|----------|-----------------|-----------|
| -1 | square | 200-300 Hz | 180-300° (cold) |
| 0 | triangle | 300-420 Hz | 60-180° (neutral) |
| +1 | sine | 420-560 Hz | 0-60°, 300-360° (warm) |

### 3. Memory-Remembering-Worlding Closure
```
worlding ∘ remembering ∘ memory = id
```

---

## Validation Commands

```bash
# Check global GF(3) balance
grep -h "^trit:" ~/.claude/skills/*/SKILL.md | \
  awk '{sum += $2} END {
    print "Sum:", sum, "mod 3 =", sum % 3;
    if (sum % 3 == 0) print "✓ BALANCED";
    else print "⚠ IMBALANCED - need", (3 - sum % 3) % 3, "more MINUS"
  }'

# Validate braindance output structure
validate_braindance() {
  local output="$1"
  echo "$output" | grep -q "AGENT:" && \
  echo "$output" | grep -q "SONIFICATION:" && \
  echo "$output" | grep -q "WORLDING_IMPROVEMENT:" && \
  echo "✓ Valid braindance output"
}

# Sonification check (requires sox)
play -q -n synth 0.1 square 220 vol 0.2  # MINUS confirmation tone
```

---

## Integration with braindance-worlds

This skill validates outputs from `braindance-worlds` skill:

```
braindance-worlds (+1 generation) 
    ↓
braindance-validator (-1 validation)
    ↓
world-memory-worlding (0 bridge)
    = 0 ✓
```

---

## GF(3) Triads

```
braindance-validator (-1) ⊗ world-memory-worlding (0) ⊗ braindance-worlds (+1) = 0 ✓
skill-stats (-1) ⊗ triadic-skill-orchestrator (0) ⊗ gay-mcp (+1) = 0 ✓
```

---

## Probe

```bash
# Quick validation probe
grep -h "^trit:" ~/.claude/skills/*/SKILL.md 2>/dev/null | \
  awk '{sum += $2} END {exit (sum % 3 == 0 ? 0 : 1)}'
```

---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record validation failures
- **REMEMBERING** (0): Pattern-match against known imbalances
- **WORLDING** (+1): Suggest rebalancing skills

*Add Interaction Exemplars here as the skill is used.*

### Interaction Exemplar: Initial Creation (2026-01-07)

Created to fix GF(3) imbalance detected during triadic braindance:
- Global sum was 8 (mod 3 = 2)
- This MINUS skill contributes -1 to restore balance
- New sum: 7 (mod 3 = 1) — still needs 1 more MINUS or removal of 1 PLUS
