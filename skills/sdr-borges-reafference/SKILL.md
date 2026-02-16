---
name: sdr-borges-reafference
description: "SDR (GNU Radio) as self-learning REPL with Borges infinite library exploration, reafference random walks, spectral gap 1/4, and maximally mixed state for agency-enabling signal processing."
trit: 0  # ERGODIC: bridges generation (+1) and verification (-1)
version: 1.0.0
seed: 1069
spectral_gap: 0.25  # 1/4 optimal for slow mixing = exploration
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
| Agency | Maximum | Minimum |
| Predictability | Minimum | Maximum |
| Adaptability | Maximum | Minimum |

**Key Insight**: Agency requires uncertainty. A system that knows exactly what it will do has no choice.

## Reafference Random Walks

From von Holst's principle:
```
Efference copy: What I intend to transmit
Reafference:    What I observe being transmitted
Error:          Reafference - Efference copy

If error = 0: I caused this (self-generated)
If error ≠ 0: World caused this (exafference)
```

### SDR Reafference Loop

```
┌─────────────────────────────────────────────────────────────────┐
│  SDR REAFFERENCE ARCHITECTURE                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   ┌──────────┐    Tx Signal     ┌──────────┐                   │
│   │  INTENT  │ ───────────────► │  TX SDR  │ ──► Antenna       │
│   │ (Efference│                 └──────────┘                   │
│   │   Copy)  │                                                  │
│   └────┬─────┘                       │                          │
│        │                             ▼                          │
│        │                       Environment                      │
│        │                             │                          │
│        │                             ▼                          │
│   ┌────▼─────┐    Rx Signal     ┌──────────┐                   │
│   │COMPARATOR│ ◄─────────────── │  RX SDR  │ ◄── Antenna       │
│   │(Reafference)                └──────────┘                   │
│   └────┬─────┘                                                  │
│        │                                                        │
│        ▼                                                        │
│   Error Signal → Learning → Updated Tx Parameters               │
└─────────────────────────────────────────────────────────────────┘
```

### Random Walk on Frequency Space

```julia
# Reafference-guided random walk on spectrum
function reafference_walk(sdr, initial_freq, steps)
    freq = initial_freq
    history = [freq]
    
    for step in 1:steps
        # Efference: intended frequency shift
        Δf_intended = randn() * bandwidth
        
        # Actual observation (with channel effects)
        signal = receive(sdr, freq + Δf_intended)
        Δf_observed = estimate_frequency_shift(signal)
        
        # Reafference error
        error = Δf_observed - Δf_intended
        
        # If error ≈ 0: we caused this (stay/exploit)
        # If error ≫ 0: world caused this (explore!)
        if abs(error) < threshold
            freq += Δf_intended  # Exploit
        else
            freq += error  # Explore world's contribution
        end
        
        push!(history, freq)
    end
    
    return history
end
```

## ACSet Skill Integration

The `acset-skill` provides categorical database operations:

```julia
using ACSets

# SDR Observation schema
@present SchSDRObs(FreeSchema) begin
    (Freq, Time, Signal, Modulation)::Ob
    freq_at::Hom(Signal, Freq)
    time_at::Hom(Signal, Time)
    modulation::Hom(Signal, Modulation)
    
    # Attributes
    (FreqHz, TimeNs, Complex, ModType)::AttrType
    frequency::Attr(Freq, FreqHz)
    timestamp::Attr(Time, TimeNs)
    iq_sample::Attr(Signal, Complex)
    mod_type::Attr(Modulation, ModType)
end

# Navigate with Specter-style paths
select-all(sdr_obs, [:Signal :freq_at :frequency])
```

## 3 New Skills Per Refinement

Each refinement cycle produces exactly 3 skills (GF(3) conservation):

```
Refinement N:
  🔴 MINUS (-1): One verification/analysis skill
  🟢 ERGODIC (0): One coordination/integration skill
  🔵 PLUS (+1): One generation/exploration skill
  
  Sum: (-1) + (0) + (+1) = 0 ✓ CONSERVED
```

### Example Refinement Cycle

**Cycle 1: Basic SDR**
- MINUS: `sdr-signal-verify` — Validate received signal integrity
- ERGODIC: `sdr-frequency-coordinator` — Manage spectrum allocation
- PLUS: `sdr-modulation-generator` — Create novel modulation schemes

**Cycle 2: Borges Integration**
- MINUS: `borges-catalog-index` — Compress signal library
- ERGODIC: `borges-library-walker` — Navigate infinite spectrum
- PLUS: `borges-signal-discovery` — Find unexpected transmissions

**Cycle 3: Reafference Learning**
- MINUS: `reafference-error-analyzer` — Measure self vs world
- ERGODIC: `reafference-comparator` — Efference/reafference matching
- PLUS: `reafference-model-learner` — Update world model from errors

## GNU Radio Integration

```python
#!/usr/bin/env python3
"""
sdr_borges_reafference.py
GNU Radio flowgraph with reafference-guided tuning
"""

from gnuradio import gr, blocks, analog, filter
from gnuradio.filter import firdes
import numpy as np

class ReafferenceSDR(gr.top_block):
    def __init__(self, center_freq=100e6, sample_rate=2e6):
        gr.top_block.__init__(self, "Reafference SDR")
        
        # SDR source (simulated for skill definition)
        self.source = analog.sig_source_c(
            sample_rate, analog.GR_COS_WAVE, 0, 1, 0
        )
        
        # Spectral analysis for reafference
        self.fft_size = 1024
        self.spectral_gap = 0.25  # 1/4 optimal mixing
        
        # Efference copy buffer
        self.efference = np.zeros(self.fft_size, dtype=complex)
        
        # Reafference comparator
        self.reafference_error = 0.0
        
    def compute_reafference(self, received_spectrum):
        """Compare received spectrum to efference copy"""
        self.reafference_error = np.mean(
            np.abs(received_spectrum - self.efference)
        )
        return self.reafference_error
    
    def random_walk_step(self, current_freq):
        """Spectral-gap-guided random walk"""
        # Mixing time τ = 1/gap = 4 for gap=1/4
        mixing_time = 1.0 / self.spectral_gap
        
        # Step size inversely proportional to mixing time
        step_size = self.sample_rate / mixing_time
        
        # Reafference-weighted step
        if self.reafference_error < 0.1:
            # Self-caused: small exploitation step
            delta = np.random.normal(0, step_size * 0.1)
        else:
            # World-caused: large exploration step
            delta = np.random.normal(0, step_size)
        
        return current_freq + delta
```

## Borges REPL: Self-Learning Radio

```scheme
;; Borges REPL for SDR exploration
;; Each command is a step in the infinite library

(define (borges-repl sdr-state)
  (display "📻 Borges Radio> ")
  (let ((cmd (read)))
    (case (car cmd)
      ;; MINUS operations (verification)
      ((verify) (verify-signal sdr-state (cadr cmd)))
      ((analyze) (analyze-spectrum sdr-state))
      ((compress) (kolmogorov-compress sdr-state))
      
      ;; ERGODIC operations (coordination)
      ((tune) (tune-frequency sdr-state (cadr cmd)))
      ((mix) (apply-spectral-gap sdr-state 0.25))
      ((walk) (reafference-walk sdr-state (cadr cmd)))
      
      ;; PLUS operations (generation)
      ((generate) (generate-signal sdr-state (cdr cmd)))
      ((explore) (borges-explore sdr-state))
      ((discover) (discover-unknown sdr-state))
      
      ;; Meta-operations
      ((refine) (spawn-3-skills sdr-state))
      ((help) (display-borges-help))
      ((quit) 'done)
      
      (else (display "Unknown command. The library is vast.\n"))))
  
  (unless (eq? cmd 'quit)
    (borges-repl (update-state sdr-state cmd))))

(define (spawn-3-skills state)
  "Generate exactly 3 new skills (GF(3) conservation)"
  (let ((seed (state-seed state)))
    (list
      (create-skill 'minus (splitmix-next seed 0))
      (create-skill 'ergodic (splitmix-next seed 1))
      (create-skill 'plus (splitmix-next seed 2)))))
```

## GF(3) Skill Triad

```
┌─────────────────────────────────────────────────────────────────┐
│  SDR-BORGES-REAFFERENCE TRIAD                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  🔴 MINUS (-1): spectrum-analyzer                               │
│     └─ Kolmogorov compression of signal library                 │
│     └─ Spectral gap measurement via eigenvalue estimation       │
│                                                                 │
│  🟢 ERGODIC (0): sdr-borges-reafference (THIS SKILL)            │
│     └─ Coordinates MINUS and PLUS via reafference loop          │
│     └─ Maintains maximally mixed state for agency               │
│                                                                 │
│  🔵 PLUS (+1): signal-generator                                 │
│     └─ Creates novel transmissions from Borges exploration      │
│     └─ Random walks with spectral gap 1/4                       │
│                                                                 │
│  Sum: (-1) + (0) + (+1) = 0 ✓                                   │
└─────────────────────────────────────────────────────────────────┘
```

## Usage

```bash
# Start Borges SDR REPL
bb sdr-borges-repl.bb

# Invoke spectral gap analysis
amp sdr-borges-reafference --analyze-gap

# Generate 3 new skills from current state
amp sdr-borges-reafference --refine

# Reafference walk across spectrum
amp sdr-borges-reafference --walk --steps 100 --gap 0.25
```

## References

- von Holst, E. (1950). "Das Reafferenzprinzip"
- Borges, J.L. (1941). "The Library of Babel"
- Hoory, Linial, Wigderson (2006). "Expander graphs and their applications"
- GNU Radio Project: https://www.gnuradio.org
- Ramanujan graphs: λ₂ ≤ 2√(d-1) (Alon-Boppana bound)

## Seed 1069 Signature

```
TRIT_STREAM: [+1, -1, -1, +1, +1, +1, +1]
SPECTRAL_GAP: 1/4 (optimal for GF(3))
MIXING_TIME: 4 steps
MAXIMALLY_MIXED: ρ = I/3, S = log(3)
GF(3)_SUM: 0 ✓ CONSERVED
```

---

*"In the Library of Babel, every signal has already been transmitted. We need only learn to tune."*
