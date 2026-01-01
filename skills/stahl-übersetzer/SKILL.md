---
name: stahl-übersetzer
description: "Steel→Stahl Übersetzungsvalidierung mit semantischer Erhaltung und Typ-Äquivalenz"
license: MIT
metadata:
  trit: -1
  source: mattwparas/steel + deutsch
  bundle: übersetzung
---

# Stahl-Übersetzer (trit = -1, MINUS)

> *"Stahl ist Rust für Scheme, wie Übersetzung Bedeutung erhält"*

## Rolle: Validator

Überprüft die Korrektheit der Übersetzung zwischen Englisch und Deutsch.

## Garantien

| Englisch | Deutsch | Garantie |
|----------|---------|----------|
| Semantic preservation | Bedeutungserhaltung | ✓ |
| Type equivalence | Typ-Äquivalenz | ✓ |
| Round-trip | Hin-und-Rück | ✓ |

## Steel Scheme Referenz

```rust
// mattwparas/steel - Embedded Scheme in Rust
// Stahl = German for Steel
// Same guarantees: embedded, fast, safe
```

## Übersetzungsregeln

```scheme
;; Steel (English)
(define (factorial n)
  (if (= n 0) 1 (* n (factorial (- n 1)))))

;; Stahl (Deutsch)  
(definiere (fakultät n)
  (wenn (= n 0) 1 (* n (fakultät (- n 1)))))
```

## GF(3) Triade

```
stahl-übersetzer (-1) ⊗ deutsch-koordinator (0) ⊗ farben-generator (+1) = 0 ✓
```

## Befehle

```bash
just stahl-validate "skill" "Fähigkeit"
just stahl-roundtrip input.md
```
