# Swan-Hedges + Plurigrid/ASI: Quick Reference Guide

**Document**: Practical implementation guide for integrating Swan-Hedges general intelligence principles into Plurigrid/ASI architecture
**Audience**: Engineering team, 5-minute read
**Date**: 2025-12-22

---

## Core Concepts Summary

### What Swan-Hedges Brings

| Concept | Problem It Solves | Plurigrid Integration |
|---------|-------------------|----------------------|
| **Semantically Closed Learning (SCL)** | "How do we make symbols meaningful?" | ACSet hypothesis graphs: queries are reasoning |
| **Compositionality** | "How do we combine learned pieces?" | Functor morphisms: algebraic skill composition |
| **Strong Typing** | "How do we catch errors before execution?" | GF(3) trits: impossible states unreachable |
| **Reflection** | "How does the system introspect?" | Statements-as-data: query ACSet about beliefs |
| **Work on Command** | "How do we adapt to new tasks instantly?" | Morphism constraints: change goal ≠ retrain |
| **Causal Structures** | "How do we reason about cause/effect?" | Evidence graphs: why did we do X? |

---

## Quick Implementation Path

### Week 1-2: Hypothesis ACSet (Foundation)

**Goal**: Build hypothesis representation that systems can reason about

```julia
# File: lib/scl_foundation.jl

@present SchHypothesis(FreeSchema) begin
  Hypothesis::Ob
  Evidence::Ob

  entailed_by::Hom(Hypothesis, Evidence)
  self_explains::Hom(Hypothesis, Hypothesis)  # Reflection!
end

@acset_type HypothesisGraph(SchHypothesis, index=[:entailed_by])

# Usage: System can query its own beliefs
explain(h::Int, acset::HypothesisGraph) =
  [e for e in acset.Evidence if h in entailed_by(e)]
```

**Test**: Can the system explain why it chose action X?
**Expected**: Lists evidence supporting hypothesis

### Week 3-4: Abduction Engine (Discovery)

**Goal**: Discover new skills from observations

```julia
# File: lib/abduction_engine.jl

function abduct_skill(observations::Vector{(input, output)})
  hypotheses = enumerate_hypotheses(observations)

  # Rank by: consistency + simplicity (description length)
  scores = [-log_description_length(h) + log_likelihood(h)
            for h in hypotheses]

  return argmax(scores)
end
```

**Test**: Given 5-10 examples of (input, output), discover the skill
**Expected**: Correct skill type identified

### Week 5-6: Open Games (Multi-Agent)

**Goal**: Formalize tripartite agent coordination

```julia
# File: lib/open_games.jl

@present SchOpenGame(FreeSchema) begin
  Input::Ob
  Output::Ob
  Payoff::Ob

  forward::Hom(Input, Output)
  payoff::Hom(Output, Payoff)
  coplay::Hom(Payoff, Input)
end

# Tripartite play
function tripartite_equilibrium(agents::Vector, max_iter=100)
  state = initial_state
  for t in 1:max_iter
    for agent in agents
      state = best_response(agent, state)
    end
    if converged(state)
      break
    end
  end

  @assert gf3_conserved(state)  # Invariant verified
  return state
end
```

**Test**: 3 agents find equilibrium; GF(3) preserved
**Expected**: sum(trits) ≡ 0 (mod 3) at equilibrium

### Week 7-8: Morphism-Based Tasks (Work on Command)

**Goal**: Execute tasks without retraining skills

```julia
# File: lib/work_on_command.jl

struct DynamicTask
  source::PossibleWorld
  target::PossibleWorld
  constraints::Vector{Symbol}  # GF(3)-preserving
end

function execute_on_command(task::DynamicTask)
  # Find skill path: source ==morphism==> target
  candidates = search_skill_space(task)

  # Verify all constraints
  best = filter(c -> satisfies_all(c, task.constraints), candidates)[1]

  return apply_skill(best, task.source)
end

# No retraining! Just different morphism constraint
task2 = DynamicTask(
  source=state,
  target=new_goal,
  constraints=[safe, efficient]
)
execute_on_command(task2)  # Uses same pre-trained skills
```

**Test**: Execute 3 different goals on same skill library
**Expected**: No retraining, instant task adaptation

---

## Key Integration Points

### 1. ACSet Hypothesis Storage

**Where**: Replace opaque agent beliefs with queryable hypothesis graph

**Before**: Agent has `belief_vector::Vector{Float64}` (opaque)
**After**: Agent has `beliefs::HypothesisGraph` (queryable)

**Benefit**: `explain(action, agent.beliefs)` returns evidence

### 2. GF(3) Invariant Enforcement

**Where**: Every skill composition, every agent move

**Before**: Skills have arbitrary trits, manual balancing
**After**: Type system enforces balance at composition time

```julia
# Old: dangerous, manual balancing
result = compose(skill_a, skill_b)  # May violate GF(3)!

# New: impossible to violate
result = compose(skill_a::SkillWithTrit[-1],
                 skill_b::SkillWithTrit[+1])
# Compiler: "Type error: needs balancing skill (trit=0)"
```

### 3. Skill Discovery Replaces Training

**Where**: Instead of supervised learning on 1M examples, abduct from 10

**Before**: `train_skill(dataset, labels, epochs=1000)`
**After**: `abduct_skill(observations)`

**Requirements**:
- Observation examples: `(input, output)` pairs
- Description length oracle: measure hypothesis complexity
- Consistency checker: does hypothesis explain all examples?

### 4. Tripartite Execution (No Change Required)

**Where**: MINUS/ERGODIC/PLUS agents already execute tripartite

**What's New**: Add formal GF(3) verification at each round
```julia
# Add to agent execution loop:
@assert (trit(minus_move) + trit(ergodic_move) + trit(plus_move)) % 3 == 0
```

---

## Metrics to Track

### 1. Skill Discovery Quality

- **Before**: `human_hours_to_implement_new_skill`
- **After**: `examples_needed_to_discover_skill` (target: <20)

### 2. Task Adaptation Speed

- **Before**: `hours_to_retrain_for_new_task`
- **After**: `seconds_to_find_new_morphism` (target: <1s)

### 3. Explainability Coverage

- **Before**: 0% (deep learning is opaque)
- **After**: % of system actions explainable via `explain(action, beliefs)`

### 4. Safety (GF(3) Violations)

- **Before**: Manual verification (error-prone)
- **After**: Automated check at composition time (zero violations)

---

## Example: "Compose PDF with Audio"

### Workflow

**Agents**: MINUS (constraints), ERGODIC (balance), PLUS (generation)

**Step 1: PLUS proposes hypothesis**
```julia
observations = [
  (pdf=doc1, audio=aud1) → video1,
  (pdf=doc2, audio=aud2) → video2,
  ...
]
hypothesis = abduct_skill(observations)
# Hypothesis: "Render PDF frames, sync with audio"
trit(hypothesis) = +1  # Generative
```

**Step 2: MINUS tries to break it**
```julia
violations = [
  (pdf=empty, audio=long) → error!
  (pdf=null, audio=normal) → crash
]
send_to_ergodic(violations)
trit(violation_evidence) = -1  # Constraint discovered
```

**Step 3: ERGODIC balances**
```julia
# Need to balance: +1 (hypothesis) + (-1) (constraint) + ? = 0
# Missing: 0 trit piece (neutral/balancing)

balancing_piece = create_boundary_handler(violations)
trit(balancing_piece) = 0

# Composite skill is now GF(3)-balanced
balanced_skill = composite(hypothesis, balancing_piece)
@assert gf3_conserved(balanced_skill)
```

**Step 4: Execute new task**
```julia
task = DynamicTask(
  source = (pdf=..., audio=...),
  target = (video=...),
  constraints = [safe_boundaries, hd_quality]
)

# No retraining! Just a different morphism constraint
execute_on_command(task)
```

---

## File Structure

```
plurigrid-asi-skillz/
├── lib/
│   ├── scl_foundation.jl          # NEW: Hypothesis graphs
│   ├── hypothesis_acset.jl        # NEW: ACSet schema
│   ├── abduction_engine.jl        # NEW: Skill discovery
│   ├── open_games.jl              # NEW: Game formalism
│   ├── tripartite_play.jl         # NEW: Agent play rules
│   ├── work_on_command.jl         # NEW: Task execution
│   ├── lenses.jl                  # NEW: Lens algebra
│   ├── skill_lens.jl              # NEW: Skill-specific lenses
│   ├── skill_discovery.jl         # Refactor + new abduction
│   └── ...existing files...
│
├── test/
│   ├── test_scl_foundation.jl     # NEW
│   ├── test_hypothesis_acset.jl   # NEW
│   ├── test_abduction.jl          # NEW
│   ├── test_open_games.jl         # NEW
│   ├── test_work_on_command.jl    # NEW
│   ├── e2e_scl_test.jl            # NEW: Full workflow
│   └── ...existing tests...
│
├── SWAN_HEDGES_TOPOLOGICAL_ASI_INTEGRATION.md  # NEW: Full framework
├── SWAN_HEDGES_QUICK_REFERENCE.md              # NEW: This file
├── README.md                      # Update with SCL section
└── ...
```

---

## Priority 1: Hypothesis ACSet

**Why First?**: All other pieces depend on it

**Definition**:
```julia
@present SchHypothesis(FreeSchema) begin
  Hypothesis::Ob
  Evidence::Ob
  Dependency::Ob

  entailed_by::Hom(Hypothesis, Evidence)
  depends_on::Hom(Evidence, Dependency)
  self_explains::Hom(Hypothesis, Hypothesis)
end
```

**Required Queries**:
- `explain(h)` → Evidence supporting h
- `evidence_for(h)` → All transitive evidence
- `self_model()` → Hypotheses about own hypotheses

**Test**: Can system answer "Why did you choose X?" for 10 decisions

---

## Priority 2: Abduction Engine

**Why Second?**: Once we have hypothesis representation, we can discover skills

**Algorithm**:
```
Input: observations = [(input_i, output_i), ...]
Output: best_hypothesis (a skill)

1. Enumerate: Generate candidate hypotheses H = {h₁, h₂, ...}
2. Rank: For each h ∈ H, compute score(h)
   score(h) = -|description(h)| + log P(observations | h)
3. Return: argmax_{h ∈ H} score(h)
```

**Test**: Discover PDF-audio skill from 10 examples

---

## Priority 3: Open Games (Tripartite)

**Why Third?**: Formalizes coordination between agents

**Minimum**:
- MINUS agent: Plays attack (tries to break hypothesis)
- ERGODIC agent: Plays arbiter (finds balance point)
- PLUS agent: Plays generator (proposes solution)

**Test**: Find equilibrium where all agents are satisfied (locally)

---

## Priority 4: Work on Command

**Why Fourth?**: Completes the loop; enables practical "no retraining" operation

**Requirement**: Given new goal (as morphism constraint), execute without retraining

**Test**: Execute 3 different goal specifications on same skill library in <5s each

---

## Risk Mitigation

### Risk 1: Abduction Complexity
**Mitigation**: Start with small skill library (10 skills), don't enumerate full space
**Fallback**: Greedy matching instead of optimal discovery

### Risk 2: GF(3) Enforcement Too Strict
**Mitigation**: Allow "partial GF(3)" initially, tighten over time
**Fallback**: Manual rebalancing if automatic fails

### Risk 3: Tripartite Equilibrium Doesn't Converge
**Mitigation**: Use gossip algorithms (faster convergence) instead of all-to-all
**Fallback**: Return best-effort after N rounds instead of true equilibrium

### Risk 4: Skill Library Bloat
**Mitigation**: Prune skills: merge similar ones, remove unused
**Fallback**: Keep only most-used 20% of discovered skills

---

## Success Metrics (16 weeks)

| Metric | Target | Measurement |
|--------|--------|-------------|
| **Skill Discovery** | 10 new skills | # discovered via abduction |
| **Task Adaptation** | <1s per task | Time to execute new morphism constraint |
| **Explainability** | >80% actions explained | Queries to `explain()` succeed |
| **GF(3) Safety** | 0 violations | Automated check passes 100% of time |
| **Performance** | <10% slower than baseline | Wall-clock time vs non-SCL system |
| **Code Coverage** | >80% | Lines covered by tests |

---

## Reading Order

1. **This file first** (5 min) - Overview
2. **SWAN_HEDGES_TOPOLOGICAL_ASI_INTEGRATION.md** (30 min) - Full framework
3. **Phase 1 code** (2 hours) - Implement hypothesis graph
4. **Test suite** (1 hour) - Verify hypothesis storage and querying

---

## Contact & Questions

- **Hypothesis representation**: Ask in `#scl-foundation` channel
- **Abduction algorithm**: See `lib/abduction_engine.jl` design doc
- **GF(3) typing**: Reference `CLOSURE_OPTIMIZATIONS_SUMMARY.md`
- **Tripartite play**: See `TRIPARTITE_AGENTS.md` for existing structure

---

## Appendix: Swan-Hedges Glossary (Translation)

| Swan-Hedges | Plurigrid Equivalent |
|-------------|---------------------|
| Semantically Closed Learning | ACSet hypothesis graphs + abduction |
| Symbol Grounding | query(hypothesis_graph) returns behavior |
| Compositionality | functor morphisms between skill categories |
| Strong Type System | GF(3) invariant enforced at composition |
| Reflection | hypotheses-as-data (query own beliefs) |
| Causality | evidence graph (why did we choose X?) |
| Abduction | lens-based skill discovery |
| Intrinsic Motivation | attention mechanism (value + novelty + GF(3)) |
| Work on Command | morphism-constrained task execution |
| 2nd Order Automation | skill identification (system discovers own gaps) |

---

**Status**: Ready for implementation
**Owner**: Engineering team
**Reviews**: Wanted from category theory experts + Plurigrid architects
