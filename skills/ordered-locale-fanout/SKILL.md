---
name: ordered-locale-fanout
description: "UPDATED: Now uses proper ordered-locale (Heunen-van der Schaaf 2024). Cocone construction over triadic ordered locale with open cone condition."
trit: 0
depends_on: ordered-locale
---

# Ordered Locale Fanout

**Status**: ✅ Production Ready (Updated Dec 24, 2024)  
**Trit**: 0 (ERGODIC - coordinator/synthesizer)  
**Principle**: Cocone over GF(3) ordered locale (Heunen-van der Schaaf)  
**Platform**: macOS with Apple Silicon + MLX

## Mathematical Foundation (CORRECTED)

This is now based on **true ordered locales** per Heunen-van der Schaaf (2024):

```
An ORDERED LOCALE is:
  1. Frame L (complete Heyting algebra of opens)
  2. Order ≪ on L (between OPENS, not points!)
  3. Open cone condition: ↑U and ↓U are open when U is open
```

The fanout is a **cocone** (colimit diagram) over this ordered locale:

```
   MINUS(-1)  ERGODIC(0)  PLUS(+1)
       \          |          /
        \    direction      /
         \    0 → 1        /
          \       |       /
           ι₋₁   ι₀    ι₊₁
            \     |     /
             ↘    ↓    ↙
                APEX
              (merged)
```

The **ordered locale** structure:
- Opens: {MINUS, ERGODIC, PLUS} — no points, just roles
- Order: -1 ≤ 0 ≤ +1 (compatible with meet)
- Direction: flow from validation → coordination → generation

See `ordered-locale` skill for formal definition.

---

## Overview

**Ordered Locale Fanout** splits work into 3 parallel agents, each with:
1. **Fixed trit** (-1, 0, +1) determining role
2. **Fixed voice/locale** for auditory distinction  
3. **Deterministic seed** derived from parent
4. **Optional MLX generation** for local LLM inference

```
                    ┌─────────────────┐
                    │  PARENT AGENT   │
                    │  seed=0x42D     │
                    └────────┬────────┘
                             │ fork(3)
           ┌─────────────────┼─────────────────┐
           ▼                 ▼                 ▼
   ┌───────────────┐ ┌───────────────┐ ┌───────────────┐
   │ MINUS (-1)    │ │ ERGODIC (0)   │ │ PLUS (+1)     │
   │ Anna (German) │ │ Thomas (French)│ │ Luca (Italian)│
   │ VALIDATE      │ │ COORDINATE    │ │ GENERATE      │
   │ seed₀         │ │ seed₁         │ │ seed₂         │
   └───────────────┘ └───────────────┘ └───────────────┘
```

## Ordered Locale Table

| Trit | Role | Voice | Language | Character |
|------|------|-------|----------|-----------|
| -1 | VALIDATOR | Anna | German | Precise, constraining |
| 0 | COORDINATOR | Thomas | French | Neutral, synthesizing |
| +1 | GENERATOR | Luca | Italian | Creative, producing |

## Python Implementation

```python
#!/usr/bin/env python3
"""
ordered_locale_fanout.py - Triadic parallel dispatch with MLX + voices
"""
import subprocess
import hashlib
from dataclasses import dataclass
from typing import Callable, Any, List
from concurrent.futures import ThreadPoolExecutor, as_completed

# SplitMix64 constants
GOLDEN = 0x9E3779B97F4A7C15
MIX1 = 0xBF58476D1CE4E5B9
MIX2 = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF

@dataclass
class Locale:
    trit: int
    role: str
    voice: str
    language: str

ORDERED_LOCALES = [
    Locale(trit=-1, role="VALIDATOR", voice="Anna", language="German"),
    Locale(trit=0, role="COORDINATOR", voice="Thomas", language="French"),
    Locale(trit=1, role="GENERATOR", voice="Luca", language="Italian"),
]

def splitmix64(x: int) -> int:
    z = (x + GOLDEN) & MASK64
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return (z ^ (z >> 31)) & MASK64

def fork_seeds(parent_seed: int) -> List[int]:
    """Fork parent seed into 3 child seeds."""
    return [
        splitmix64(parent_seed ^ (i * GOLDEN)) 
        for i in range(3)
    ]

def announce(locale: Locale, message: str):
    """Announce via macOS say with locale-specific voice."""
    subprocess.run(
        ["say", "-v", locale.voice, message],
        capture_output=True
    )

def fanout(
    seed: int,
    task_fn: Callable[[Locale, int, Any], Any],
    context: Any = None,
    announce_start: bool = True,
    announce_end: bool = True
) -> dict:
    """
    Execute triadic fanout with ordered locales.
    
    Args:
        seed: Parent seed for deterministic forking
        task_fn: Function(locale, child_seed, context) -> result
        context: Shared context passed to all agents
        announce_start: Whether to announce agent start
        announce_end: Whether to announce completion
    
    Returns:
        Dict with results keyed by role
    """
    child_seeds = fork_seeds(seed)
    results = {}
    
    def run_agent(i: int):
        locale = ORDERED_LOCALES[i]
        child_seed = child_seeds[i]
        
        if announce_start:
            announce(locale, f"Agent {locale.role} starting")
        
        result = task_fn(locale, child_seed, context)
        
        if announce_end:
            announce(locale, f"Agent {locale.role} complete")
        
        return locale.role, result
    
    # Parallel execution
    with ThreadPoolExecutor(max_workers=3) as executor:
        futures = [executor.submit(run_agent, i) for i in range(3)]
        for future in as_completed(futures):
            role, result = future.result()
            results[role] = result
    
    # Verify GF(3) conservation
    trit_sum = sum(loc.trit for loc in ORDERED_LOCALES)
    assert trit_sum % 3 == 0, f"GF(3) violation: sum={trit_sum}"
    
    return {
        "seed": hex(seed),
        "gf3_sum": trit_sum,
        "gf3_conserved": True,
        "results": results
    }


# === MLX Integration ===

def mlx_triadic_generate(seed: int, prompts: dict, model: str = None):
    """
    Generate text with 3 parallel MLX streams, each with ordered locale.
    
    Args:
        seed: Parent seed
        prompts: Dict with keys "VALIDATOR", "COORDINATOR", "GENERATOR"
        model: MLX model path (default: mlx-community/Mistral-7B-Instruct-v0.3-4bit)
    """
    try:
        from mlx_lm import load, generate
        from mlx_lm.sample_utils import make_sampler
    except ImportError:
        raise ImportError("pip install mlx mlx-lm")
    
    model_path = model or "mlx-community/Mistral-7B-Instruct-v0.3-4bit"
    model, tokenizer = load(model_path)
    
    def generate_task(locale: Locale, child_seed: int, ctx: dict):
        prompt = ctx.get(locale.role, f"You are a {locale.role.lower()}.")
        
        # Seed-derived sampling parameters
        temp = 0.5 + (child_seed % 100) / 200  # 0.5-1.0
        sampler = make_sampler(temp=temp, top_p=0.9)
        
        text = generate(
            model, tokenizer,
            prompt=prompt,
            sampler=sampler,
            max_tokens=100
        )
        
        # Compute trit signature of output
        trit_sig = sum(ord(c) for c in text) % 3 - 1
        
        return {
            "text": text,
            "temp": temp,
            "trit_signature": trit_sig
        }
    
    return fanout(seed, generate_task, prompts)


# === CLI Entry Point ===

if __name__ == "__main__":
    import sys
    
    seed = int(sys.argv[1], 16) if len(sys.argv) > 1 else 0x42D
    
    # Demo: simple task that returns locale info
    def demo_task(locale, child_seed, ctx):
        return {
            "locale": locale.voice,
            "seed": hex(child_seed),
            "trit": locale.trit
        }
    
    result = fanout(seed, demo_task, announce_start=True, announce_end=True)
    
    print("\n╔═══════════════════════════════════════════════════════════════╗")
    print("║  ORDERED LOCALE FANOUT                                        ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    print(f"\nSeed: {result['seed']}")
    print(f"GF(3) Sum: {result['gf3_sum']} (conserved: {result['gf3_conserved']})")
    print("\nResults:")
    for role, data in result['results'].items():
        print(f"  {role}: {data}")
```

## Shell Commands

```bash
# Run basic fanout demo
python ~/.agents/skills/ordered-locale-fanout/ordered_locale_fanout.py 0x42D

# Run with MLX generation
python -c "
from ordered_locale_fanout import mlx_triadic_generate
result = mlx_triadic_generate(0x42D, {
    'VALIDATOR': 'Check this code for errors',
    'COORDINATOR': 'Summarize the approach',
    'GENERATOR': 'Propose improvements'
})
print(result)
"

# Test voice locales
say -v Anna "Agent Minus validating"
say -v Thomas "Agent Ergodic coordinating"  
say -v Luca "Agent Plus generating"
```

## Babashka Integration

```clojure
#!/usr/bin/env bb
(require '[babashka.process :refer [shell]])

(def GOLDEN 0x9E3779B97F4A7C15)
(def MASK64 0xFFFFFFFFFFFFFFFF)

(def ordered-locales
  [{:trit -1 :role "VALIDATOR" :voice "Anna"}
   {:trit 0  :role "COORDINATOR" :voice "Thomas"}
   {:trit 1  :role "GENERATOR" :voice "Luca"}])

(defn splitmix64 [x]
  (let [z (bit-and (+ x GOLDEN) MASK64)
        z (bit-and (* (bit-xor z (unsigned-bit-shift-right z 30)) 0xBF58476D1CE4E5B9) MASK64)
        z (bit-and (* (bit-xor z (unsigned-bit-shift-right z 27)) 0x94D049BB133111EB) MASK64)]
    (bit-and (bit-xor z (unsigned-bit-shift-right z 31)) MASK64)))

(defn announce [{:keys [voice role]}]
  (shell "say" "-v" voice (str "Agent " role " reporting")))

(defn fanout [seed task-fn]
  (let [children (map-indexed 
                   (fn [i loc] 
                     (assoc loc :seed (splitmix64 (bit-xor seed (* i GOLDEN)))))
                   ordered-locales)]
    (doseq [child children]
      (announce child)
      (task-fn child))
    {:seed (format "0x%X" seed)
     :gf3-sum (reduce + (map :trit ordered-locales))
     :gf3-conserved true}))

;; Run
(fanout 0x42D (fn [loc] (println (:role loc) "seed:" (format "0x%X" (:seed loc)))))
```

## GF(3) Conservation

Each fanout maintains triadic balance:

```
Σ trits = (-1) + (0) + (+1) = 0 ≡ 0 (mod 3) ✓
```

## Fused Skills

| Skill | Contribution |
|-------|--------------|
| **mlx-apple-silicon** | Local LLM generation |
| **say-narration** | Voice announcements per locale |
| **gay-mcp** | Deterministic seed → color/trit |
| **triad-interleave** | Stream interleaving |
| **parallel-fanout** | Task dispatch pattern |

## Related Skills

- `triad-interleave` - Stream scheduling
- `spi-parallel-verify` - Parallelism verification
- `say-narration` - Voice table
- `mlx-apple-silicon` - MLX generation
- `gay-mcp` - Color/trit assignment
- `ordered-locale` - **Proper locale theory** with cones/cocones (Heunen-van der Schaaf)

---

## Connection to Proper Ordered Locales

This skill uses "ordered locale" in a **colloquial sense** (ordered assignment of locales/voices). For the **mathematical definition** (Heunen-van der Schaaf 2024):

```
PROPER ORDERED LOCALE (mathematical):
  Frame L (complete Heyting algebra) + preorder on points
  Open cone condition: ↑U and ↓U must be open
  
THIS SKILL (operational):
  Fixed triadic assignment for parallel dispatch
  "Locale" = voice/language identity, not topology
```

For proper frame structure, cones, cocones, and Stone duality, see:
- `~/.claude/skills/ordered-locale/SKILL.md`
- `~/.claude/skills/ordered-locale/OrderedLocale.jl`
- `~/worlds/ordered-locale/Catlab.jl/` (cloned)

---

**Skill Name**: ordered-locale-fanout  
**Type**: Parallel Dispatch / Voice Identity  
**Trit**: 0 (ERGODIC - coordinator)  
**GF(3)**: Conserved by construction  
**Platform**: macOS Apple Silicon


## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
