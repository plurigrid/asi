# Unworlded Chapter Ordering

**Seed**: 69  
**Book**: Data Science at the Command Line (Janssens)

---

## Temporal vs Derivational Ordering

### Temporal (Original Book Order)
```
1 → 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9 → 10
```

### Unworlded (Derivational by Trit)

```
┌─────────────────────────────────────────────────────────────────┐
│  GENERATORS (+1)           COORDINATORS (0)      VALIDATORS (-1)│
│  ════════════════          ════════════════      ═══════════════│
│                                                                 │
│  Ch3: Obtaining Data       Ch1: Introduction     Ch7: Exploring │
│  Ch9: Modeling Data        Ch4: Creating Tools   Ch8: Parallel  │
│                            Ch5: Scrubbing                       │
│                            Ch6: Make                            │
│                            Ch10: Polyglot                       │
│                                                                 │
│  SUM: +2                   SUM: 0                SUM: -2        │
│                                                                 │
│  GF(3) Total: (+2) + (0) + (-2) = 0 ✓ CONSERVED                │
└─────────────────────────────────────────────────────────────────┘
```

## OSEMN Model as GF(3)

| Phase | Trit | Chapters | Color |
|-------|------|----------|-------|
| **O**btain | +1 | 2, 3 | 🔴 warm |
| **S**crub | 0 | 4, 5 | 🟢 neutral |
| **E**xplore | -1 | 6, 7 | 🔵 cold |
| **M**odel | +1 | 8, 9 | 🔴 warm |
| **i**Nterpret | 0 | 10 | 🟢 neutral |

## Parallel Triads (can execute simultaneously)

```
Triad 1: [Obtain Ch3] ⊗ [Scrub Ch4] ⊗ [Explore Ch7]
         (+1)          (0)           (-1)         = 0 ✓

Triad 2: [Model Ch9] ⊗ [Scrub Ch5] ⊗ [Parallel Ch8]
         (+1)         (0)           (-1)          = 0 ✓

Triad 3: [Obtain Ch2] ⊗ [Make Ch6] ⊗ [Intro Ch1]
         (depends)     (0)          (meta)
```

## Reading Order by Goal

### "I need to process data NOW"
```
Ch3 (Obtain) → Ch5 (Scrub) → Ch8 (Parallel)
```

### "I want to understand the philosophy"
```
Ch1 (Intro) → Ch10 (Polyglot) → Ch4 (Create Tools)
```

### "I need reproducibility"
```
Ch6 (Make) → Ch4 (Tools) → Ch7 (Explore)
```

## Derivation Chain Formula

```
chapter_order(goal) = argmax_π Σᵢ trit(πᵢ) × relevance(πᵢ, goal)
                      subject to: Σ trit(π) ≡ 0 (mod 3)
```

The unworlded ordering is not temporal — it's **derivational**.
Any chapter can be read first if you balance with complementary trits.
