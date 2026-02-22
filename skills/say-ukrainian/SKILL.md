---
name: say-ukrainian
description: Non-Ukrainian voices speak Ukrainian. Every context event gets voiced — no silence, no skips. Maximally informative counterfactual narration.
version: 1.2.0
---

# Say Ukrainian

Foreign voices speak Ukrainian. Not translations — *refractions*. Utterance length matches shared context: word, fragment, or phrase. Every event gets voiced. No silence, no skips.

**Trit**: +1 (PLUS) **Color**: #FFD700

## Voices

Only Enhanced/Premium. Pick by GF(3) trit, rotate round-robin within class. Rate 130–160 WPM.

| Trit | Voices |
|------|--------|
| -1 (MINUS) | Alice (Enhanced), Emma (Enhanced), Federica (Enhanced), Paola (Enhanced) |
| 0 (ERGODIC) | Ava (Premium), Samantha (Enhanced), Allison (Enhanced) |
| +1 (PLUS) | Nathan (Enhanced), Evan (Enhanced), Nicky (Enhanced), Noelle (Enhanced) |

## Forbidden

- **Lesya** (uk-UA) — collapses counterfactual
- **Milena** (ru-RU) — political charge
- Compact/super-compact voices
- Novelty voices, Daniel (en-GB)

## Transliteration

Feed Cyrillic first. Only fall back to Latin when the voice produces silence or reads letter names.

**Single-letter patch**: Standalone single Cyrillic letters (і, у, з, я…) trigger "cyrillic letter X" announcements in non-Ukrainian voices. Pipe all text through `scripts/patch-singles.sh` before TTS — it replaces only isolated single-letter tokens with their phonetic sound, leaving words untouched.

```sh
echo "річ із вершків і зірок" | scripts/patch-singles.sh
# → "річ із вершків ee зірок"  (only standalone і patched)
```

**Known Cyrillic support** (tested):
- Cyrillic works (with patch-singles): Ava (Premium), Nathan (Enhanced), Samantha (Enhanced)
- Cyrillic silent — full Latin transliteration: Alice (Enhanced), Federica (Enhanced), Emma (Enhanced), Paola (Enhanced)

Full Latin transliteration table (only for silent voices):

| Cyrillic | Latin | | Cyrillic | Latin |
|----------|-------|-|----------|-------|
| і, и | ee | | ч | ch |
| у | oo | | ш | sh |
| е | eh | | щ | shch |
| г | h | | ж | zh |
| я | yah | | ь | y or omit |
| ю | yoo | | є | yeh |

## Examples

From Richard Siken, *Litany in Which Certain Things Are Crossed Out*:

| # | Spoken | Siken line | Voice |
|---|--------|------------|-------|
| 1 | "Розплющуєш очі — лише галявина з оленями" | you open your eyes only a clearing with deer in it | Alice |
| 2 | "Дозволь мені зробити річ із вершків і зірок" | let me make a thing of cream and stars | Ava |
| 3 | "Чорне небо поколоте дрібними вогниками" | a black sky prickled with small lights | Nathan |
| 4 | "Дерев'яні зали наче труни" | the wooden halls like caskets | Federica |
| 5 | "У тебе очі як ліхтарі" | you get eyes like flashlights | Samantha |

The voice is the counterfactual. The accent refracts the line into остранення — a foreign mouth on familiar words. Cyrillic until it breaks, then patch with Latin.

## Open Games Integration

```
  ctx ──│ Game Gᵢ │──→ action
  🔊 ←──│ say-ukr  │←── response

coplay(response) = refract(response) |> speak(foreign_voice)
```

Voice is the optic. Accent refracts utility into остранення.

## GF(3) Conservation

```
Σ trits ≡ 0 (mod 3) across session
say-narration (-1) ⊗ say-ukrainian (+1) ⊗ open-games (0) = 0
```
