---
name: teglon-mathpix
description: 'Ruby gem for Mathpix OCR:'
metadata:
  interface_ports:
  - GF(3) Triads
---
# Teglon Mathpix Skill

> Transform mathematical images to LaTeX with security-first design

**Source**: [TeglonLabs/mathpix-gem](https://github.com/TeglonLabs/mathpix-gem)  
**Trit**: −1 (MINUS)  
**Substrate**: Continuous (NCA/Visual)

## Overview

Ruby gem for Mathpix OCR:
- Image → LaTeX conversion
- Chemistry structures → SMILES
- Documents → Markdown
- Security-first API design

## α/β/γ Diff Structure

| Arrow | Mathpix Meaning | Operation |
|-------|-----------------|-----------|
| α (−1) | OCR extraction | `Image → LaTeX` |
| β (0) | Format transformation | `LaTeX → MathML` |
| γ (+1) | Verification | `render(LaTeX) ≈ Image` |

## Ruby Integration

```ruby
require 'mathpix'

client = Mathpix::Client.new(
  app_id: ENV['MATHPIX_APP_ID'],
  app_key: ENV['MATHPIX_APP_KEY']
)

result = client.process_image('equation.png')
puts result.latex  # "E = mc^2"
```

## Upstream Diff

TeglonLabs original:
- Security-first credential handling
- Balanced ternary checkpoints for processing state
- GF(3) conservation in batch processing

---

## End-of-Skill Interface

## GF(3) Triads

```
teglon-mathpix (-1) ⊗ mathpix-ocr (0) ⊗ free-monad-gen (+1) = 0 ✓
teglon-mathpix (-1) ⊗ just-monad (0) ⊗ gay-mcp (+1) = 0 ✓
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
