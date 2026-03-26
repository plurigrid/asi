---
name: nhero-scramble
description: Derangement-based medication name scrambling for nhero. No medication maps to its own initial letter. Full derangement with GF(3) conservation. Append-only index — medications can be added but never removed from the scramble table.
version: 0.1.0
trit: 0
color: "#00FF00"
tags: [nhero, scramble, derangement, privacy, gf3]
---

# nhero-scramble

Derangement-based name scrambling. Append-only.

## Rules

1. No medication maps to its own initial letter (derangement)
2. GF(3) sum of assigned letters must equal world trit (-1 for H)
3. New medications are appended, never removed (append-only)
4. Letter assignment maximizes Hamming distance from H and natural initial

## CLI

```bash
python3 hero_scramble.py table              # show full table
python3 hero_scramble.py lookup q           # q → Vyvanse
python3 hero_scramble.py reverse Vyvanse    # Vyvanse → q
python3 hero_scramble.py set x 400          # set Magnesium to 400mg
python3 hero_scramble.py add Melatonin      # auto-assign deranged letter
```

## Append-Only Protocol

The scramble index is append-only:
- `add` appends a new (letter, medication) pair
- `set` updates dosage but never removes the mapping
- No `remove` or `delete` operation exists
- Historical mappings are preserved for audit trail
- On-chain: `keccak256(scramble_index)` is the commitment

## Parent
Part of the [nhero](../nhero/SKILL.md) hierarchy.
