---
name: farben-generator
description: "Deterministische Farbenerzeugung mit deutschen Farbnamen (Fröhlich.jl)"
license: MIT
metadata:
  trit: +1
  source: Gay.jl + deutsch
  bundle: übersetzung
---

# Farben-Generator (trit = +1, PLUS)

> *"Fröhlich.jl: Deterministische Farbenerzeugung auf Deutsch"*

## Rolle: Generator

Erzeugt deterministische Farben mit deutschen Namen.

## SpaltMisch64 Algorithmus

```julia
# Gay.jl → Fröhlich.jl
# SplitMix64 → SpaltMisch64

funktion spaltmisch64(keim, index)
    GOLDEN = 0x9E3779B97F4A7C15
    zustand = (keim + index * GOLDEN) & MASKE64
    z = zustand
    z = ((z ⊻ (z >> 30)) * MISCH1) & MASKE64
    z = ((z ⊻ (z >> 27)) * MISCH2) & MASKE64
    rückgabe z ⊻ (z >> 31)
ende
```

## Farben (GF(3) Trit-Zuordnung)

| Deutsch | English | Hex | Trit |
|---------|---------|-----|------|
| Rot | Red | #D8267F | +1 (PLUS) |
| Grün | Green | #26D826 | 0 (ERGODISCH) |
| Blau | Blue | #2668D8 | -1 (MINUS) |

## Farbton → Trit

```
Farbton 0-60°, 300-360° → +1 (PLUS, warm)
Farbton 60-180°         →  0 (ERGODISCH, neutral)
Farbton 180-300°        → -1 (MINUS, kalt)
```

## Befehle

```bash
just farbe-bei 42 --keim 0x42D
just palette 12 --deutsch
just fröhlich-test
```

## GF(3) Triade

```
stahl-übersetzer (-1) ⊗ deutsch-koordinator (0) ⊗ farben-generator (+1) = 0 ✓
```

## Beispiel

```
╔═══════════════════════════════════════════════════════════════════╗
║  FRÖHLICH.JL: Deterministische Farbenerzeugung                      ║
╚═══════════════════════════════════════════════════════════════════╝

Keim: 0x42D

─── Palette (3 Farben) ───
  1: #D8267F (Trit=+1) ROT
  2: #26D826 (Trit=0)  GRÜN
  3: #2668D8 (Trit=-1) BLAU

GF(3): (+1) + (0) + (-1) = 0 ✓ ERHALTEN
```
