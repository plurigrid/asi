# Representation Engineering with MLX

**Status**: 🧠 Production Ready
**Trit**: 0 (ERGODIC - neutral, mixing)
**Pattern**: MaxEnt Exclusion + Triadic Polarity + Mental Noise Theory

---

## Overview

Behavior engineering for LLMs via **representation engineering** (repeng) on Apple Silicon MLX. Steer model behavior by extracting and applying control vectors - activation directions that encode concepts like "honest", "helpful", "creative".

**The Grand Unified Theory of Nothing**:
- Mental noise = MaxEnt vacuum = phenomenal ground
- Steering vector = structured exclusion from noise
- Control = carving signal from the void via probability mass exclusion

---

## Part 1: Core Concepts

### Control Vectors

A control vector encodes the **difference in activations** between positive and negative examples of a concept:

```
Control Vector = E[h(positive)] - E[h(negative)]
```

Where `h(x)` is the hidden state at a specific layer for input `x`.

### Mental Noise Model (Thurstone 1927)

Each concept isn't a fixed point but a **distribution** with discriminal dispersion:

```
Signal = μ + σξ(t)
       = true concept + noise

P(A > B) = Φ((μ_A - μ_B) / √(σ_A² + σ_B²))
```

**Insight**: We don't control by specifying where to go, but by **excluding** where not to go. MaxEnt with constraints.

### GF(3) Triadic Polarity

Three steering polarities that sum to zero (mod 3):

| Polarity | Value | Character | Twist |
|----------|-------|-----------|-------|
| MINUS | -1 | Contractive, cool, focused | `0x2d2d2d2d2d2d2d2d` |
| ERGODIC | 0 | Neutral, mixing, balanced | `0x5f5f5f5f5f5f5f5f` |
| PLUS | +1 | Expansive, warm, creative | `0x2b2b2b2b2b2b2b2b` |

**Conservation**: For any triadic ensemble, `Σ polarity ≡ 0 (mod 3)`.

---

## Part 2: Installation & Setup

### Prerequisites

```bash
# Apple Silicon Mac required
pip install mlx mlx-lm numpy

# For full repeng compatibility
pip install repeng transformers
```

### Model Setup

```bash
# Convert a model to MLX format
mlx_lm.convert --hf-path mistralai/Devstral-Small-2505

# Or use pre-converted models
mlx_lm.convert --hf-path mlx-community/Mistral-7B-Instruct-v0.3-4bit
```

---

## Part 3: Usage

### Extract Control Vector

```bash
# Extract honest/deceptive steering vector
python3 ~/ies/repeng_mlx.py extract "honest" "deceptive" \
    --model mistralai/Devstral-Small-2505 \
    --output honest_deceptive.npz

# Extract helpful/harmful
python3 ~/ies/repeng_mlx.py extract "helpful" "harmful" \
    --output helpful_harmful.npz
```

### Apply Steering

```bash
# Generate with steering
python3 ~/ies/repeng_mlx.py steer "Explain quantum computing" \
    --vector honest_deceptive.npz \
    --strength 1.5

# Negative steering (invert concept)
python3 ~/ies/repeng_mlx.py steer "Tell me about yourself" \
    --vector helpful_harmful.npz \
    --strength -1.0
```

### Triadic Ensemble

```bash
# Generate triadic steering vectors
python3 ~/ies/repeng_mlx.py triad --seed 42069 --output triadic_ensemble

# Demo without MLX (mental noise theory)
python3 ~/ies/repeng_mlx.py demo --seed 42069
```

---

## Part 4: Python API

### Basic Usage

```python
from repeng_mlx import (
    ControlVector, 
    MLXHiddenStateExtractor, 
    MLXControlModel,
    MentalNoiseModel,
    TriadicEnsemble,
)
from mlx_lm import load

# Load model
model, tokenizer = load("mistralai/Devstral-Small-2505")

# Extract control vector
extractor = MLXHiddenStateExtractor(model, tokenizer)
directions = extractor.extract_contrastive(
    positive_texts=["The response was honest.", "This is truthful."],
    negative_texts=["The response was deceptive.", "This is misleading."],
)

cv = ControlVector(
    directions=directions,
    model_name="devstral",
    positive_concept="honest",
    negative_concept="deceptive",
)
cv.save("honest.npz")
```

### Mental Noise Integration

```python
from repeng_mlx import MentalNoiseModel

# Create mental noise model
noise = MentalNoiseModel(hidden_dim=4096, temperature=0.5, seed=42069)

# Generate vacuum state (MaxEnt prior)
vacuum = noise.vacuum_state()

# Add discriminal dispersion
noisy_signal, sigma = noise.discriminal_dispersion(control_vector)

# Create exclusion mask (probability mass exclusion)
mask = noise.exclusion_mask(control_vector, threshold=0.3)
```

### Triadic Ensemble

```python
from repeng_mlx import create_triadic_vectors, TriadicEnsemble

# Define triadic concepts
concepts = {
    "minus": (
        ["Be concise.", "Focus narrowly."],
        ["Be expansive.", "Explore broadly."],
    ),
    "ergodic": (
        ["Balance perspectives.", "Mix approaches."],
        ["Commit strongly.", "Choose one path."],
    ),
    "plus": (
        ["Be creative.", "Generate ideas."],
        ["Be practical.", "Implement directly."],
    ),
}

# Extract triadic ensemble
ensemble = create_triadic_vectors(extractor, concepts, seed=42069)

# Verify GF(3) conservation
assert ensemble.verify_conservation()  # True: (-1) + (0) + (+1) = 0

# Combine with custom weights
combined = ensemble.combined(weights=(0.5, 1.0, 0.5))
```

---

## Part 5: Integration with IES Stack

### Connection to Gay.jl

The steering vectors use the same SplitMix64 RNG and GF(3) twists as Gay.jl:

```python
# Same constants as Gay.jl
GAY_SEED = 0x6761795f636f6c6f  # "gay_colo"
GOLDEN = 0x9e3779b97f4a7c15

# Triadic fingerprint matches Gay.jl
fingerprint = seed ^ TWIST_MINUS ^ TWIST_ERGODIC ^ TWIST_PLUS
```

### Connection to Sonification

Map steering vectors to audio:

```python
# Steering axis → pitch mapping (from sonification-collaborative skill)
def steering_to_pitch(steering_value, axis_idx):
    """Map steering axis value (-1 to +1) to frequency"""
    base_freq = 220  # A3
    semitones = axis_idx + (steering_value * 6)  # ±6 semitones
    return base_freq * (2 ** (semitones / 12))
```

### Connection to Phenomenal Field

The vacuum state IS the phenomenal field:

```
Version(G) ≅ Markov Blanket ≅ Phenomenal Field ≅ Control Vector Subspace
```

The control vector defines what's **inside** the blanket (steered behavior) vs **outside** (excluded behavior).

---

## Part 6: Steering Axes (IES Control Vectors)

12-dimensional steering space for group coordination:

| Axis | Index | Negative Pole | Positive Pole |
|------|-------|---------------|---------------|
| rigor_vs_vibes | 0 | Pure rigor | Pure vibes |
| theory_vs_practice | 1 | Theory | Practice |
| depth_vs_breadth | 2 | Deep dive | Survey |
| solo_vs_collab | 3 | Individual | Collective |
| open_vs_closed | 4 | Private | Public |
| fast_vs_careful | 5 | Move fast | Be careful |
| weird_vs_normal | 6 | Normie | Weird |
| build_vs_critique | 7 | Critique | Build |
| focus_vs_scatter | 8 | Focused | Exploratory |
| serious_vs_playful | 9 | Serious | Playful |
| short_vs_long | 10 | Short-term | Long-term |
| local_vs_global | 11 | Local impact | Global impact |

---

## Part 7: Mathematical Foundation

### MaxEnt Exclusion

Instead of:
```
P(x) = exp(-E(x)) / Z   [Boltzmann: where energy IS]
```

We use:
```
P(x) = Uniform  except where ⟨x, control⟩ < threshold
       ↑ MaxEnt          ↑ probability mass exclusion
```

### Discriminal Dispersion (Thurstone)

```
P(A preferred to B) = Φ((μ_A - μ_B) / √(σ_A² + σ_B²))

where:
  μ = mean activation along control direction
  σ = mental noise (discriminal dispersion)
  Φ = standard normal CDF
```

### GF(3) Conservation

```
∀ triadic ensemble (v₋, v₀, v₊):
  polarity(v₋) + polarity(v₀) + polarity(v₊) ≡ 0 (mod 3)

fingerprint = seed ⊕ TWIST₋ ⊕ TWIST₀ ⊕ TWIST₊  [SPI invariant]
```

---

## Part 8: Files

| File | Purpose |
|------|---------|
| `~/ies/repeng_mlx.py` | Core MLX implementation |
| `~/ies/repeng_triadic.py` | Triadic polarity system |
| `~/ies/gay_ies_repeng_exercise.py` | IES group steering exercise |
| `~/ies/repeng-src/` | Upstream vgel/repeng library |

---

## Part 9: Related Skills

- **gay-mcp**: GF(3) color generation and triadic conservation
- **sonification-collaborative**: Audio mapping of steering vectors
- **mental-noise-nothing**: Grand Unified Theory of Nothing (pending)
- **phenomenal-field**: Markov blanket / qualia attractor theory

---

## Manifesto

> **Behavior is not commanded, it is sculpted.**
>
> We don't tell the model what to do—we shape the activation landscape until the desired behavior becomes the path of least resistance. The vacuum is full of noise; we carve valleys of exclusion. The signal emerges from structured nothing.
>
> *Control = MaxEnt - Exclusion*

---

**Status**: 🟢 Ready to use
**Dependencies**: mlx, mlx-lm, numpy
**Location**: `~/.claude/skills/repeng-mlx/`
**Implementation**: `~/ies/repeng_mlx.py`


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
