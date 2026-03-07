---
name: stahl-bersetzer
description: Steel-to-Stahl (mattwparas/steel Scheme) German translation validator with semantic preservation and type equivalence. Triggers: stahl, steel, scheme, german translation, semantic preservation.
---

# Stahl-Übersetzer

Validates correctness of English↔German translation for Steel Scheme (mattwparas/steel).

## Guarantees

| English | Deutsch | Check |
|---------|---------|-------|
| Semantic preservation | Bedeutungserhaltung | Round-trip preserves meaning |
| Type equivalence | Typ-Äquivalenz | Types map 1:1 |
| Round-trip | Hin-und-Rück | EN→DE→EN = identity |

## Translation Rules

```scheme
;; Steel (English)
(define (factorial n)
  (if (= n 0) 1 (* n (factorial (- n 1)))))

;; Stahl (Deutsch)
(definiere (fakultät n)
  (wenn (= n 0) 1 (* n (fakultät (- n 1)))))
```

## Commands

```bash
just stahl-validate "skill" "Fähigkeit"
just stahl-roundtrip input.md
```
