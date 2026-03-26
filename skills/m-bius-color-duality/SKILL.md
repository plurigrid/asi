---
name: möbius-color-duality
description: Möbius inversion for Gay.jl color spaces — recovers seeds from color distributions
---

# Möbius Color Duality

Numerical Möbius inversion applied to color spaces: given observed color distributions (global aggregates), recover the generating seed (local structure).

## Module

`lib/gay_möbius_inversion.py` (490 lines) — not currently found in the repo tree. If it has been moved or renamed, search for `ColorMöbiusInverter` or `TriadicColorInverter`.

### Key Classes

- `ColorMöbiusInverter` — numerical forward/backward inversion for color spaces. Forward: seed to color indices to structures. Backward: structures to color distributions to recovered seed.
- `TriadicColorInverter` — extends inversion to GF(3) ternary color states.

### Usage

```python
from lib.gay_möbius_inversion import ColorMöbiusInverter

inverter = ColorMöbiusInverter()
# Forward pass: seed -> color distribution
distribution = inverter.forward(seed)
# Backward pass: distribution -> recovered seed
recovered = inverter.invert(distribution)
```

## Integration

This fills the "Inversion (Duality)" layer of the sparsification spine (was at 1.6% coverage). The system can generate color structures but this module enables the reverse — recovering seeds from observed colorizations.
