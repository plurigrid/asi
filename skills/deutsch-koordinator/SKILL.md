---
name: deutsch-koordinator
description: "Koordinator für Deutsch-Englisch Übersetzung mit GF(3) Routing"
license: MIT
metadata:
  trit: 0
  source: übersetzung
  bundle: übersetzung
---

# Deutsch-Koordinator (trit = 0, ERGODIC)

> *"Der Koordinator routet zwischen Sprachen"*

## Rolle: Koordinator

Vermittelt zwischen englischen und deutschen Begriffen.

## Wörterbuch

| English | Deutsch | Invariant |
|---------|---------|-----------|
| skill | Fähigkeit | ✗ |
| thread | Faden | ✗ |
| color | Farbe | ✗ |
| seed | Samen/Keim | ✗ |
| trit | Trit | ✓ |
| GF(3) | GF(3) | ✓ |
| SplitMix64 | SpaltMisch64 | ✗ |

## Technische Begriffe

| English | Deutsch |
|---------|---------|
| monoidal category | monoidale Kategorie |
| string diagram | Strang-Diagramm |
| functor | Funktor |
| morphism | Morphismus |
| composition | Komposition |
| parallel | parallel |
| sequential | sequentiell |

## Befehle

```bash
just deutsch "translate this skill"
just englisch "übersetze diese Fähigkeit"
```

## GF(3) Triade

```
stahl-übersetzer (-1) ⊗ deutsch-koordinator (0) ⊗ farben-generator (+1) = 0 ✓
```
