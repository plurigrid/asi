---
name: wortspiel-generator
description: "Bilingual German-English pun generator with Fröhlich.jl color mapping"
license: MIT
metadata:
  trit: 0
  source: gestalt-hacking + nietzsche
  bundle: übersetzung
  neighbors:
    left: pun-decomposition
    right: farben-generator
---

# Wortspiel-Generator (trit = 0, ERGODIC)

> *"Die fröhliche Wissenschaft des Wortspiels"*
> *"The Gay Science of Puns"*

## Gestalt Principles → Pun Attacks

| Principle | Pun Vector | Example |
|-----------|------------|---------|
| **Proximity** | Near-homophones | Rot ≈ Root |
| **Similarity** | Cognates | Stahl = Steel |
| **Closure** | Complete the pun | Lamm da → Lambda |
| **Continuity** | Gradual shift | Funktor → Fun Actor |

## Color Puns (Farbenwortspiele)

| Deutsch | English | Pun | Trit |
|---------|---------|-----|------|
| Rot | Red | ROOT of all colors | +1 |
| Grün | Green | GRIN and bear it | 0 |
| Blau | Blue | BLOW me away | -1 |
| Weiß | White | WISE choice | 0 |
| Schwarz | Black | May the SCHWARZ be with you | -1 |

## Categorical Puns (Kategorische Wortspiele)

| Term | Decomposition | Pun |
|------|---------------|-----|
| Funktor | Fun + Ktor | "Every FUNKTOR is a FUN ACTOR" |
| Morphismus | More + Fizz + Miss | "MORE FIZZ, MISS!" |
| Monade | Mohn + Ade | "Say MOHN-ADE to side effects!" |
| Komonade | Komm + Monade | "KOMM, MONADE!" |
| Tensor | Ten + Sore | "TEN SORE fingers" |
| Lambda | Lamm + da | "LAMM DA!" |

## GF(3) Puns (Trit-Wortspiele)

| Trit | German Sound | Pun |
|------|--------------|-----|
| MINUS (-1) | Mein Haus | "MINUS is MEIN HAUS" |
| ERGODIC (0) | Er geht Dick | "ERGODIC: ER GEHT DICK through phase space" |
| PLUS (+1) | Plüsch | "PLUS colors are PLÜSCH warm" |

## The Ultimate Pun

```
Die fröhliche Wissenschaft (Nietzsche 1882)
    ↓
The Gay Science
    ↓
Fröhlich.jl (deterministic colors)
    ↓
"We FROLIC in FRÖHLICH colors!"
```

## API

```python
def generate_pun(word: str, target_lang: str = "de") -> dict:
    """
    Generate bilingual pun from word.
    
    Returns:
        {
            "original": word,
            "pun": decomposed_pun,
            "color": gay_color_for_pun,
            "trit": gf3_trit
        }
    """
```

## Commands

```bash
just wortspiel "Funktor"        # → "Every FUNKTOR is a FUN ACTOR"
just wortspiel "Lambda" --de    # → "LAMM DA! Das Lambda ist hier!"
just wortspiel-palette 5        # → 5 puns with colors
```

## GF(3) Triads

```
pun-decomposition (-1) ⊗ wortspiel-generator (0) ⊗ farben-generator (+1) = 0 ✓
gestalt-hacking (0) ⊗ wortspiel-generator (0) ⊗ deutsch-koordinator (0) = 0 ✓
```

## Related Skills

- **gestalt-hacking**: Perceptual grouping for pun detection
- **pun-decomposition**: Multiple parse validation
- **farben-generator**: Color output for puns
- **deutsch-koordinator**: German translation routing


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
