---
name: sdr-borges-reafference
description: 'SDR (GNU Radio) as self-learning REPL with Borges infinite library exploration, reafference random walks, spectral gap 1/4, and maximally mixed state for agency-enabling signal processing.'
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# SDR-Borges-Reafference: Agency-Enabling Signal Processing

> "The Library of Babel contains every possible radio transmission."
> — Borges meets GNU Radio

## Core Concept

**SDR as Infinite Library**: Software Defined Radio is a Borges library where:
- Every frequency is a book
- Every modulation scheme is a language
- Every signal is a text awaiting interpretation
- The spectral gap determines how fast you find the book you seek

## Spectral Gap 1/4: The Sweet Spot

```
┌─────────────────────────────────────────────────────────────────┐
│  SPECTRAL GAP AND MIXING TIME                                   │
├─────────────────────────────────────────────────────────────────┤
│  Gap = 0:    τ_mix = ∞    (stuck, no exploration)               │
│  Gap = 1/4:  τ_mix = 4    (balanced exploration/exploitation)   │
│  Gap = 1/2:  τ_mix = 2    (fast mixing, less diversity)         │
│  Gap = 1:    τ_mix = 1    (instant mixing, no memory)           │
└─────────────────────────────────────────────────────────────────┘

WHY 1/4?
- Alon-Boppana bound for d=3 regular graphs: λ₂ ≤ 2√2 ≈ 2.83
- Normalized gap = (d - λ₂)/d ≈ 0.25 for Ramanujan graphs
- This is OPTIMAL for 3-way (GF(3)) systems!
```

## Maximally Mixed State: Agency Through Ignorance

The **maximally mixed state** ρ = I/d is:
- Maximum entropy: S(ρ) = log(d)
- No information about which eigenstate you're in
- **Agency interpretation**: Complete freedom of choice

```julia
# Maximally mixed state in 3-dimensional GF(3) space
ρ_max = [1/3 0 0; 0 1/3 0; 0 0 1/3]

# Purity: tr(ρ²) = 1/3 (minimal for d=3)
# Von Neumann entropy: S = log(3) ≈ 1.585 bits

# AGENCY MEANING:
# - You can become MINUS, ERGODIC, or PLUS with equal probability
# - No prior commitment constrains your action space
# - Maximum optionality = maximum agency
```

### What Maximally Mixed Gets Us

| Property | Maximally Mixed | Pure State |
|----------|-----------------|------------|
| Entropy | log(3) = 1.585 | 0 |
| Purity | 1/3 | 1 |
| Agency | Maximu