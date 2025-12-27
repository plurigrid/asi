# Dynamic Sufficiency Integration Guide

## GF(3) Triad

The dynamic-sufficiency skill forms a complete triad:

```
dynamic-sufficiency (-1) ⊗ skill-dispatch (0) ⊗ skill-installer (+1) = 0 ✓
     VALIDATOR              COORDINATOR           GENERATOR
```

## How to Enable Never-Act-Without-Sufficiency

### Option 1: AGENTS.md Directive

Add to your project's `AGENTS.md`:

```markdown
## Skill Sufficiency Requirement

Before undertaking ANY action, verify skill sufficiency using the
dynamic-sufficiency protocol:

1. **Infer causal state** from the intended action
2. **Compute coverage** against loaded skills
3. **Gate execution** on ≥95% coverage

If coverage is insufficient:
- Attempt to load missing skills via `skill` tool
- If loading fails, explain what skills are needed
- NEVER proceed with coverage < 50%

Load the skill for details:
```
skill dynamic-sufficiency
```
```

### Option 2: Pre-Message Hook (Programmatic)

```python
from sufficiency import (
    EpsilonMachine, 
    pre_action_gate,
    coverage_score,
    Verdict
)

class SufficiencyEnforcedAgent:
    def __init__(self):
        self.em = EpsilonMachine()
        self.loaded_skills = set()
    
    def process_message(self, message: str):
        # 1. Predict actions from message
        actions = self.predict_actions(message)
        
        # 2. Check sufficiency for each
        for action in actions:
            verdict, coverage = pre_action_gate(
                action, 
                self.loaded_skills, 
                self.em
            )
            
            if verdict == Verdict.ABORT:
                return self.refuse_insufficient(action, coverage)
            
            if verdict == Verdict.LOAD_MORE:
                self.load_skills(coverage.missing)
        
        # 3. Proceed with execution
        return self.execute(message)
```

### Option 3: Decorator Pattern

```python
from sufficiency import require_sufficiency

@require_sufficiency(min_coverage=0.95)
def create_mcp_server(language: str, features: list):
    """This function won't execute without sufficient skills."""
    ...
```

## Skill Loading Triggers

When dynamic-sufficiency detects insufficient coverage, it can trigger:

1. **Explicit skill loading**: 
   ```
   skill load gay-mcp spi-parallel-verify bisimulation-game
   ```

2. **Triad completion**:
   ```python
   # If loading gay-mcp (+1) and spi-parallel-verify (-1),
   # auto-suggest triad-interleave (0) for GF(3) = 0
   ```

3. **Skill discovery**:
   ```
   skill discover --domain=haskell --operation=mcp
   ```

## Causal State Examples

| Action Pattern | Causal State | Required Skills |
|----------------|--------------|-----------------|
| "create haskell mcp" | `code:haskell:mcp:write` | `ghc, mcp-builder, gay-mcp` |
| "verify spi across languages" | `verify:spi:polyglot` | `spi-parallel-verify, polyglot-spi` |
| "scrape web for docs" | `web:scrape:read` | `firecrawl, exa` |
| "edit julia acset" | `code:julia:acset:transform` | `julia-gay, acsets, specter-acset` |

## ε-Machine Learning

The sufficiency system learns from experience:

```python
# After successful action
epsilon_machine.add_observation(action, skills_used, success=True)

# After failure
epsilon_machine.add_observation(action, skills_used, success=False)

# Query learned sufficiency
required = epsilon_machine.minimal_sufficient_skills(new_action)
```

Over time, the ε-machine refines its model of which skills are truly necessary for each task class.

## Metrics Dashboard

```
╔═══════════════════════════════════════════════════════════════════╗
║  SUFFICIENCY METRICS                                              ║
╠═══════════════════════════════════════════════════════════════════╣
║  Statistical Complexity (C_μ): 3.42 bits                          ║
║  Causal States Observed: 47                                       ║
║  Average Coverage at Action: 92.3%                                ║
║  Actions Gated (ABORT): 3                                         ║
║  Skills Dynamically Loaded: 12                                    ║
║  GF(3) Triads Completed: 8                                        ║
╚═══════════════════════════════════════════════════════════════════╝
```

## Santa Fe Institute References

1. **Computational Mechanics** (Crutchfield & Young)
   - Causal states as minimal sufficient statistics
   - ε-machines for optimal prediction

2. **Effective Complexity** (Gell-Mann & Lloyd)
   - Complexity = length of compressed regularities
   - Skill complexity = minimal skill set for task class

3. **Predictive Information** (Bialek, Nemenman, Tishby)
   - I_pred ≈ (K/2) log N for K-dimensional skill space
   - Measures information about future from past

4. **Information Geometry** (Amari, Ay et al.)
   - Fisher metric on skill configurations
   - Sufficient statistics preserve geometric structure
