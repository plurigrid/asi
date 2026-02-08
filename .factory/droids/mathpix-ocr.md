---
name: mathpix-ocr
description: Mathpix OCR for LaTeX extraction with balanced ternary checkpoints
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# mathpix-ocr - Balanced Ternary OCR Pipeline for LaTeX → ACSet Extraction

## Overview

Integrates [TeglonLabs/mathpix-gem](https://github.com/TeglonLabs/mathpix-gem) for mathematical OCR with the music-topos ACSet parallel rewriting system. Uses seed 1069 balanced ternary checkpoints for resilient PDF batch processing.

## The 1069 Connection

mathpix-gem shares our canonical seed:

```ruby
# From mathpix-gem/lib/mathpix/balanced_ternary.rb
# 1×3⁶ - 1×3⁵ - 1×3⁴ + 1×3³ + 1×3² + 1×3¹ + 1×3⁰ = 1069
SEED_1069_PATTERN = [+1, -1, -1, +1, +1, +1, +1].freeze

# Semantics progression:
#   +1 (high confidence) → -1 (descent) → -1 (exploration) →
#   +1 (recovery) → +1 (convergence) → +1 (stability) → +1 (completion)
```

This maps directly to our TAP states and GF(3) arithmetic.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Mathpix OCR → ACSet Pipeline                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   PDF/Image                 Balanced Ternary              ACSet Schema      │
│      │                      Checkpoints                        │            │
│      ▼                           │                             ▼            │
│  ┌────────┐    ┌─────────────────┴─────────────────┐    ┌──────────────┐   │
│  │Mathpix │───▶│ +1 → -1 → -1 → +1 → +1 → +1 → +1 │───▶│ @present Sch │   │
│  │  OCR   │    │ ─── ─── ─── ─── ─── ─── ───       │    │   Type::Ob   │   │
│  └────────┘    │ 729  -243 -81  +27  +9   +3   +1  │    │   Term::Ob   │   │
│      │         └─────────────────┬─────────────────┘    └──────────────┘   │
│      │                           │                             │            │
│      ▼                           ▼                             ▼            │
│  LaTeX AST                 Confidence                   Colored ACSet       │
│ 