# Phase 1 Integration: Playwright-Unworld + Swan-Hedges SCL

## Overview

The Playwright-Unworld skill is designed to integrate with the Swan-Hedges SCL (Symbolic Computing Layer) framework, which consists of three core subsystems:

1. **Abduction Engine** (`abduction_engine.jl`) - Learn selector patterns from observations
2. **Hypothesis Graphs** (`hypothesis_graph.jl`) - Trace and explain selector derivation decisions
3. **Attention Mechanism** (`attention_mechanism.jl`) - Prioritize tests by novelty and learning value

This document explains the integration architecture and how data flows between Playwright-Unworld and Phase 1 modules.

---

## Architecture Layers

### Layer 1: Observation (Abduction)

**What happens**: When Playwright attempts to locate UI elements, observations are recorded.

```
Browser Interaction
       ↓
AbductionObservation (selector tried, success/failure, DOM context)
       ↓
observe_dom() function records multiple selector attempts
       ↓
Vector<AbductionObservation> sent to abduction engine
```

**Key structures**:

```julia
struct AbductionObservation
    timestamp::UInt64
    selector_tried::String
    success::Bool
    dom_context::Dict{String, Any}
    element_role::Union{String, Nothing}
    element_text::Union{String, Nothing}
    parent_classes::Vector{String}
    siblings_count::Int
    confidence::Float64
end
```

**Example flow**:

```julia
# For email field, try multiple selectors
candidates = [
    "[data-testid=email-input]",      # testid - most specific
    "[name=email]",                    # name attribute
    "[type=email]",                    # type attribute
    ".email-field",                    # class
    "#email"                           # id - least reliable
]

observations = observe_dom(skill, "email-input", candidates)
# Returns: 5 observations, one for each selector attempted
```

**Scoring**: Each selector is scored by robustness:
- `[data-testid=...]` → 1.0 (most reliable)
- `[role=...]` → 0.95
- `has-text()` → 0.85
- `[name=...]` → 0.75
- `[class=...]` → 0.70
- `[id=...]` → 0.60
- `nth-child()` → 0.1 (least reliable)

---

### Layer 2: Hypothesis Formation (Abduction + Explanation)

**What happens**: From observations, form the BEST EXPLANATION for success/failure.

```
Vector<AbductionObservation>
       ↓
hypothesize_selector() - abductive reasoning
       ↓
SelectorHypothesis (decision, confidence, evidence, alternatives)
       ↓
explain_selector_choice() - generate human-readable explanation
       ↓
String explanation sent to hypothesis graph module
```

**Key structures**:

```julia
struct SelectorHypothesis
    component::String                           # "email-input"
    decision_path::Vector{String}               # ["[data-testid=...]"]
    confidence::Float64                         # 1.0
    evidence::Vector{AbductionObservation}      # successful attempts
    alternatives_considered::Vector{Tuple}      # rejected selectors
    timestamp::UInt64
end
```

**Abductive Reasoning Process**:

1. **Observation**: Selector X works, selector Y fails
2. **Best Explanation**: X is more specific/robust than Y
3. **Hypothesis**: Use X for this component in future tests
4. **Validation**: If X fails later, reject hypothesis and form new one

**Example**:

```julia
hypothesis = hypothesize_selector([
    AbductionObservation("[data-testid=email]", true, confidence=1.0),
    AbductionObservation("[name=email]", true, confidence=0.95),
    AbductionObservation("nth-child(1)", false, confidence=0.1),
])

# Result: hypothesis suggests "[data-testid=email]" with 100% confidence

explanation = explain_selector_choice(hypothesis)
# Output:
#   Selector Choice Explanation
#   ===========================
#   Component: email-input
#   Chosen: [data-testid=email]
#   Confidence: 100%
#
#   Supporting Evidence:
#     1. Tried: [data-testid=email]
#        Success: true
#        Role: textbox
```

---

### Layer 3: Test Ranking (Attention Mechanism)

**What happens**: Tests are prioritized based on curiosity-driven exploration.

```
TripartiteTestSuite (MINUS/ERGODIC/PLUS)
       ↓
rank_test_priority() with attention metrics
       ↓
Vector<AttentionRanking> (novelty, learning_value, priority)
       ↓
select_test_execution_order() maintains GF(3) balance
       ↓
Vector<TestCase> execution order
```

**Key structures**:

```julia
struct AttentionRanking
    test_id::String
    novelty::Float64        # 0-1: how unexplored?
    learning_value::Float64 # 0-1: how informative?
    priority::Float64       # composite score
    reason::String
    polarity::Int8          # GF(3) trit: -1, 0, +1
end
```

**Novelty Scoring**: Tests for untested components get higher scores

```julia
# Component "email-input" never tested before
novelty = 1.0  # Highest novelty

# Component "email-input" tested 3 times
novelty = 0.3  # Lower novelty
```

**Learning Value Scoring**:
- **MINUS tests** (refutation): 0.8 - Error handling teaches system boundaries
- **ERGODIC tests** (neutral): 0.6 - Happy paths confirm basic functionality
- **PLUS tests** (confirmation): 0.9 - Advanced features reveal system capabilities

**Priority Formula**:

```
MINUS:   priority = 0.6 × novelty + 0.4 × learning_value
ERGODIC: priority = 0.5 × novelty + 0.5 × learning_value
PLUS:    priority = 0.4 × novelty + 0.6 × learning_value
```

**GF(3) Conservation**: The execution order maintains balance

```julia
rankings = rank_test_priority(suite)
# Result: [Test1 (minus), Test2 (plus), Test3 (ergodic), ...]

execution_order = select_test_execution_order(bridge, suite)
# Result: Tests reordered by priority, GF(3) sum ≡ 0 (mod 3)
```

---

## Data Flow Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                    Playwright Automation                         │
└───────────────────────┬─────────────────────────────────────────┘
                        │
                        ▼
        ┌──────────────────────────────┐
        │  AbductionObservation        │  ← DOM interaction records
        │  - selector tried            │
        │  - success/failure           │
        │  - confidence score          │
        └────────┬─────────────────────┘
                 │
                 ▼
    ┌────────────────────────────────────┐
    │   Phase 1: Abduction Engine        │ (when available)
    │  ABD_ENGINE.abduct_skill()         │
    │  → Learn selector patterns         │
    │  → Update skill ontology           │
    └────────────┬──────────────────────┘
                 │
                 ▼
        ┌──────────────────────────────┐
        │  SelectorHypothesis          │  ← Decision explanation
        │  - decision_path             │
        │  - confidence                │
        │  - supporting evidence       │
        │  - alternatives rejected     │
        └────────┬─────────────────────┘
                 │
                 ▼
    ┌────────────────────────────────────┐
    │  Phase 1: Hypothesis Graphs        │ (when available)
    │  HYPOTHESIS_GRAPH.update()         │
    │  → Trace selector decisions        │
    │  → Explain choices to user         │
    └────────────┬──────────────────────┘
                 │
                 ▼
        ┌──────────────────────────────┐
        │  TripartiteTestSuite         │  ← GF(3) balanced tests
        │  - MINUS tests               │
        │  - ERGODIC tests             │
        │  - PLUS tests                │
        └────────┬─────────────────────┘
                 │
                 ▼
    ┌────────────────────────────────────┐
    │  Phase 1: Attention Mechanism      │ (when available)
    │  ATTENTION.rank_novelty()          │
    │  → Estimate component novelty      │
    │  → Score learning value            │
    │  → Rank tests by curiosity         │
    └────────────┬──────────────────────┘
                 │
                 ▼
        ┌──────────────────────────────┐
        │  AttentionRanking            │  ← Prioritized tests
        │  - novelty [0-1]             │
        │  - learning_value [0-1]      │
        │  - priority [0-1]            │
        │  - reason                    │
        └────────┬─────────────────────┘
                 │
                 ▼
    ┌────────────────────────────────────┐
    │  select_test_execution_order()     │  ← Execution order
    │  - maintains GF(3) balance         │
    │  - sorted by priority              │
    └────────────┬──────────────────────┘
                 │
                 ▼
        ┌──────────────────────────────┐
        │  Test Execution              │  ← Run tests
        │  Measure success/failure      │
        │  Record outcomes              │
        └──────────────────────────────┘
```

---

## Integration Points

### 1. Observation → Abduction Engine

**Current Implementation**: Generates observations in `observe_dom()`

**Phase 1 Connection** (commented, ready to uncomment):

```julia
# In update_learning_from_observation():
if bridge.abduction_engine_available
    hypothesis_updates = ABD_ENGINE.abduct_skill(
        skill_name = bridge.skill_name,
        observations = observations,
        component = component
    )
end
```

**What this enables**:
- Automatic learning of selector preferences per website
- Skill ontology updates after each test run
- Pattern discovery across multiple sites

### 2. Hypothesis → Hypothesis Graphs

**Current Implementation**: Generates hypotheses in `hypothesize_selector()`

**Phase 1 Connection** (commented, ready to uncomment):

```julia
# In update_learning_from_observation():
if bridge.abduction_engine_available
    HYPOTHESIS_GRAPH.add_node(
        id = "selector_$(component)_$(uuid4())",
        hypothesis = hypothesis,
        explanation = explain_selector_choice(hypothesis),
        timestamp = time_ns()
    )
end
```

**What this enables**:
- Full trace of why each selector was chosen
- Debugging when selectors fail
- Transfer learning between similar sites

### 3. Tests → Attention Mechanism

**Current Implementation**: Ranks tests in `rank_test_priority()`

**Phase 1 Connection** (commented, ready to uncomment):

```julia
# In select_test_execution_order():
if bridge.attention_mechanism_available
    refined_rankings = ATTENTION.rank_novelty(
        tests = [test_map[r.test_id] for r in rankings],
        visited_components = tested_components,
        learning_history = skill_learning_history
    )
end
```

**What this enables**:
- Optimal test ordering based on agent curiosity
- Automatic discovery of untested edge cases
- Progressive skill improvement

---

## Phase 1 Module Requirements

Once Phase 1 modules are created, they should implement:

### ABD_ENGINE Interface

```julia
module ABD_ENGINE

function abduct_skill(
    skill_name::String,
    observations::Vector{AbductionObservation},
    component::String
)::Dict{String, Any}
    # Returns: updated skill ontology
    # - new_selectors: Dictionary of component → best selectors
    # - confidence_scores: Per-selector confidence
    # - learning_rate: How much did we learn?
end

end
```

### HYPOTHESIS_GRAPH Interface

```julia
module HYPOTHESIS_GRAPH

function add_node(
    id::String,
    hypothesis::SelectorHypothesis,
    explanation::String,
    timestamp::UInt64
)::String
    # Returns: node ID for later retrieval
end

function explain_path(
    component::String
)::Vector{String}
    # Returns: decision path explaining why this selector was chosen
end

end
```

### ATTENTION Interface

```julia
module ATTENTION

function rank_novelty(
    tests::Vector{TestCase},
    visited_components::Set{String},
    learning_history::Dict{String, Float64}
)::Vector{AttentionRanking}
    # Returns: refined rankings based on learning history
end

end
```

---

## GF(3) Conservation Through Integration

**Key Invariant**: GF(3) is conserved at every stage.

```
AbductionObservations
  ↓ (each observation has polarity info)
SelectorHypothesis
  ↓ (hypothesis inherits polarity from best evidence)
TripartiteTestSuite
  ↓ (MINUS=-1, ERGODIC=0, PLUS=+1)
AttentionRanking
  ↓ (preserves polarity from source test)
Execution Order
  ↓ (sum of polarities ≡ 0 mod 3)
Test Results
```

**Verification**:

```julia
# At any stage, check conservation
polarity_sum = sum(ranking.polarity for ranking in rankings)
@assert polarity_sum % 3 == 0  # Always true by construction
```

---

## Usage Example: Complete Workflow

```julia
using PlaywrightUnworld, PlaywrightPhase1Integration

# 1. Create skill
skill = create_playwright_skill("myapp", 0x42D, "https://myapp.com")

# 2. Initialize bridge to Phase 1
bridge = SCLBridge("myapp")

# 3. Observe DOM interactions
candidates = ["[data-testid=login]", "[role=button]", "button"]
observations = observe_dom(skill, "login-button", candidates)

# 4. Form hypothesis about best selector
hypothesis = hypothesize_selector(observations)
println(explain_selector_choice(hypothesis))

# 5. Learn from observation
updated_hypothesis = update_learning_from_observation(
    bridge,
    "login-button",
    observations
)

# 6. Generate test suite (GF(3) balanced)
suite = generate_tripartite_tests(0x42D, "login", ["click", "type", "submit"])

# 7. Rank tests by attention
rankings = rank_test_priority(suite, Set{String}())

# 8. Select execution order
execution_order = select_test_execution_order(bridge, suite)

# 9. Execute tests (in optimal order)
for test in execution_order
    println("Running $(test.name) (priority)")
    # Actually run the test...
end
```

---

## Status

| Component | Status | Notes |
|-----------|--------|-------|
| AbductionObservation | ✅ Complete | Designed and tested |
| SelectorHypothesis | ✅ Complete | Ready for Phase 1 |
| AttentionRanking | ✅ Complete | GF(3) conserving |
| SCLBridge | ✅ Complete | Interface defined |
| Phase 1 Modules | ⏳ Pending | Awaiting creation |
| Integration Tests | ✅ Complete | 12 test categories |
| Documentation | ✅ Complete | This file |

---

## Next Steps

1. **Create Phase 1 modules** in `../../../ies/plurigrid-asi-skillz/lib/`:
   - `scl_foundation.jl` - Base types and utilities
   - `abduction_engine.jl` - ABD_ENGINE module above
   - `attention_mechanism.jl` - ATTENTION module above

2. **Uncomment integration points** in `phase1_integration.jl`:
   - Lines 215-220: ABD_ENGINE connection
   - Lines 240-250: HYPOTHESIS_GRAPH connection
   - Lines 310-320: ATTENTION connection

3. **Run integration tests**:
   ```bash
   just test-phase1
   ```

4. **Deploy as unified skill**:
   ```bash
   just build
   ```

---

## See Also

- [playwright_unworld.jl](./lib/playwright_unworld.jl) - Core implementation
- [tripartite_testing.jl](./lib/tripartite_testing.jl) - Test generation
- [phase1_integration.jl](./lib/phase1_integration.jl) - This integration layer
- [SKILL.md](./SKILL.md) - Full specification
- [justfile](./justfile) - Development commands

