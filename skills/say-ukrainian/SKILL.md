---
name: say-ukrainian
description: Non-Ukrainian voices speak Ukrainian via macOS say command. Load when voicing Ukrainian text through foreign TTS voices for counterfactual narration or ostranення effect.
---

# Say Ukrainian

Foreign voices speak Ukrainian. Not translations -- refractions. Utterance length matches shared context. Every event gets voiced.

## Voices

Only Enhanced/Premium. Rate 130-160 WPM.

| Category | Voices |
|----------|--------|
| Cold | Alice (Enhanced), Emma (Enhanced), Federica (Enhanced), Paola (Enhanced) |
| Neutral | Ava (Premium), Samantha (Enhanced), Allison (Enhanced) |
| Warm | Nathan (Enhanced), Evan (Enhanced), Nicky (Enhanced), Noelle (Enhanced) |

## Forbidden

- **Lesya** (uk-UA) -- collapses counterfactual
- **Milena** (ru-RU) -- political charge
- Compact/super-compact voices
- Novelty voices, Daniel (en-GB)

## Transliteration

Feed Cyrillic first. Only fall back to Latin when the voice produces silence or reads letter names.

**Single-letter patch**: Standalone single Cyrillic letters trigger "cyrillic letter X" announcements in non-Ukrainian voices. Pipe all text through `scripts/patch-singles.sh` before TTS.

```sh
echo "rich iz vershkiv i zirok" | scripts/patch-singles.sh
```

**Cyrillic support** (tested):
- Cyrillic works (with patch-singles): Ava (Premium), Nathan (Enhanced), Samantha (Enhanced)
- Cyrillic silent -- full Latin transliteration: Alice (Enhanced), Federica (Enhanced), Emma (Enhanced), Paola (Enhanced)

Full Latin transliteration table (only for silent voices):

| Cyrillic | Latin | | Cyrillic | Latin |
|----------|-------|-|----------|-------|
| i, y | ee | | ch | ch |
| u | oo | | sh | sh |
| e | eh | | shch | shch |
| h | h | | zh | zh |
| ya | yah | | soft sign | y or omit |
| yu | yoo | | ye | yeh |

## Examples

| # | Spoken | Source line | Voice |
|---|--------|------------|-------|
| 1 | "Rozplyushchuyesh ochi -- lyshe halyavyna z olenyamy" | you open your eyes only a clearing with deer in it | Alice |
| 2 | "Dozvol meni zrobyty rich iz vershkiv i zirok" | let me make a thing of cream and stars | Ava |
| 3 | "Chorne nebo pokolote dribnymy vohnykamy" | a black sky prickled with small lights | Nathan |
| 4 | "Derevyani zaly nache truny" | the wooden halls like caskets | Federica |
| 5 | "U tebe ochi yak likhtarni" | you get eyes like flashlights | Samantha |
