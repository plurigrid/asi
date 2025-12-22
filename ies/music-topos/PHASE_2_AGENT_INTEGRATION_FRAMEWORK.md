# Phase 2: Agent Integration Framework

**Date**: December 22, 2025 (Prepared ahead)
**Phase**: 2 of 4 (Weeks 27-28)
**Status**: 🔵 PLANNED - Implementation Beginning
**Objective**: Connect agents to spectral architecture for theorem discovery and proof orchestration

---

## Overview

Phase 2 enables autonomous agents to leverage the spectral architecture for:
1. **Health-aware exploration** - Check system state before theorem discovery
2. **Comprehension-guided search** - Use random walk regions to guide proof attempts
3. **Resource-efficient navigation** - Cache proofs via bidirectional index with non-backtracking constraint
4. **Automatic remediation** - Trigger gap-preserving edge removal when needed

---

## Agent Architecture

### Agent Components

```
Agent Instance
├── Health Monitor (uses Spectral Gap Analyzer)
├── Theorem Discovery Engine (uses Spectral Random Walker)
├── Proof Navigator (uses Bidirectional Index)
├── Status Tracker (uses Continuous Inverter)
└── Remediation Manager (uses Safe Rewriting Advisor + Möbius Filter)
```

### Integration Flow

```
Agent Goal: Prove Theorem T
    ↓
[1] Health Check ─→ Gap = Spectral Gap Analyzer.analyze()
    │
    ├─ Gap < 0.25? → Yes → [4] Remediation Path
    │                     ↓
    │                 Recommend fixes
    │                 Continue after fix or timeout
    │
    └─ Gap ≥ 0.25? → Yes → Continue
    │
[2] Comprehension Discovery ─→ Spectral Random Walker.comprehension_discovery()
    ↓
    Region = comprehension["comprehension_regions"][T.id]

[3] Proof Navigation ─→ Bidirectional Index.evaluate_backward(index, T.id)
    ↓
    proofs = Related proofs from region
    cache = Non-backtracking navigation check

[4] Proof Attempt Strategy
    ├─ Try proofs from comprehension region (high co-visitation)
    ├─ Use cached paths (O(1) lookup from bidirectional index)
    ├─ Track proof consumption (LHoTT linear evaluation)
    └─ If gap drops → Queue remediation

[5] Success/Failure
    ├─ Success → Log covisitation patterns for learning
    ├─ Failure (Gap degraded) → [4] Remediation Path
    └─ Timeout → [4] Remediation Path
```

---

## Implementation Stages

### Stage 1: Basic Health Monitoring (Week 27.1)

**Goal**: Agents check system health before proof attempts

```julia
# In agent proof attempt function:
using SpectralAnalyzer

@agent function attempt_proof(theorem_id::Int, goal::String) -> Bool
    # First: Check system health
    gap_analysis = SpectralAnalyzer.analyze_all_provers()
    current_gap = gap_analysis["overall_gap"]

    if current_gap < 0.20  # Very degraded
        @warn "System unhealthy (gap=$current_gap), attempt may fail"
        return false
    elseif current_gap < 0.25  # Degraded but acceptable
        @info "System degraded (gap=$current_gap), proceeding with caution"
    else
        @info "System healthy (gap=$current_gap), proceeding"
    end

    # Continue with proof attempt...
    # ... rest of proof logic ...
end
```

**Expected Outcome**:
- Agents aware of system state
- Proof attempts logged with gap context
- Patterns emerge showing gap → success rate correlation

---

### Stage 2: Comprehension-Guided Discovery (Week 27.2)

**Goal**: Use random walk comprehension regions to guide theorem discovery

```julia
using SpectralAnalyzer
using SpectralRandomWalk
using BidirectionalIndex

@agent function discover_related_theorems(theorem_id::Int) -> Vector{Int}
    # Check system health
    gap = SpectralAnalyzer.analyze_all_provers()["overall_gap"]

    # Get comprehension region
    comprehension = SpectralRandomWalk.comprehension_discovery(adjacency, gap)
    region = get(comprehension["comprehension_regions"], theorem_id, [])

    if isempty(region)
        @warn "No comprehension region found for theorem $theorem_id"
        return []
    end

    # Sample related theorems from region
    num_to_sample = min(10, length(region))
    related = sample(region, num_to_sample)

    # Bias sampling toward theorems with higher co-visitation
    co_visit_scores = comprehension["co_visit_matrix"][theorem_id, related]
    weighted_related = related[sortperm(co_visit_scores, rev=true)]

    return weighted_related
end
```

**Expected Outcome**:
- Agents discover 5-10 related theorems per query
- Related theorems grouped by comprehension region
- Co-visitation scores guide proof attempt priority

---

### Stage 3: Efficient Navigation Caching (Week 27.3)

**Goal**: Use bidirectional index for O(1) proof lookup with LHoTT resource tracking

```julia
using BidirectionalIndex

# Initialize once per agent
const proof_index = BidirectionalIndex.create_index(theorems, proofs)

@agent function find_proofs_for_theorem(theorem_id::Int) -> Vector{Int}
    # O(1) lookup via bidirectional index
    proofs = BidirectionalIndex.evaluate_backward(proof_index, theorem_id)

    # Check non-backtracking property (LHoTT compatibility)
    if !BidirectionalIndex.check_non_backtracking(proof_index)
        @warn "Non-backtracking violated, evaluation may not be linear"
    end

    return proofs
end

# Track proof consumption for resource-aware execution
struct ProofConsumption
    proof_id::Int
    consumed::Bool
    attempts::Int
    success::Bool
end

consumed_proofs = Dict{Int, ProofConsumption}()

@agent function apply_proof(proof_id::Int, goal::String) -> Bool
    # Check if proof already consumed
    if haskey(consumed_proofs, proof_id) && consumed_proofs[proof_id].consumed
        @info "Proof $proof_id already consumed (linear evaluation)"
        return false
    end

    # Apply proof
    success = try_proof(proof_id, goal)

    # Track consumption
    consumed_proofs[proof_id] = ProofConsumption(
        proof_id,
        success,  # Mark consumed if successful
        1,
        success
    )

    return success
end
```

**Expected Outcome**:
- Proof lookup: < 0.1 seconds per query
- Linear evaluation tracking: Memory-efficient resource use
- Cache hit rate: 95%+ after warm-up

---

### Stage 4: Automatic Remediation (Week 28.1)

**Goal**: Detect gap degradation and trigger remediation

```julia
using ContinuousInversion
using SafeRewriting
using MobiusFilter

# Global state for gap tracking
mutable struct AgentState
    gap_baseline::Float64
    gap_current::Float64
    remediation_pending::Bool
    last_analysis_time::Float64
end

agent_state = AgentState(0.25, 0.25, false, time())

@agent function proof_attempt_with_monitoring(theorem::String, proof_attempts::Vector) -> Bool
    # Measure gap before attempt
    gap_before = SpectralAnalyzer.analyze_all_provers()["overall_gap"]

    # Attempt proofs
    success = false
    for proof in proof_attempts
        if apply_proof(proof, theorem)
            success = true
            break
        end
    end

    # Measure gap after attempt
    gap_after = SpectralAnalyzer.analyze_all_provers()["overall_gap"]
    agent_state.gap_current = gap_after

    # If gap degraded significantly, trigger remediation
    gap_drop = gap_before - gap_after
    if gap_drop > 0.05  # More than 0.05 drop
        @warn "Significant gap drop detected: $gap_before → $gap_after"
        queue_remediation(gap_before, gap_after)
    end

    return success
end

function queue_remediation(gap_before::Float64, gap_after::Float64)
    # Diagnose problem
    tangled = MobiusFilter.filter_tangled_paths(adjacency)

    # Generate fix
    plan = SafeRewriting.generate_rewrite_plan(adjacency, gap_before)

    # Queue for human review/application
    suggestions = ContinuousInversion.suggest_remediation(
        "lean4",  # example prover
        gap_before,
        gap_after
    )

    println("Remediation suggestions:")
    for sugg in suggestions
        println("  - $sugg")
    end
end
```

**Expected Outcome**:
- Gap drops detected within 5 attempts
- Remediation suggestions generated automatically
- Fix approval workflow established

---

## Agent Skill Imports

```julia
module AgentSkills

using SpectralAnalyzer
using MobiusFilter
using BidirectionalIndex
using SafeRewriting
using SpectralRandomWalk
using ContinuousInversion

export
    # Health monitoring
    check_system_health,

    # Theorem discovery
    discover_related_theorems,
    get_comprehension_region,

    # Proof navigation
    find_proofs_for_theorem,
    apply_proof_resource_aware,

    # Remediation
    detect_gap_degradation,
    suggest_fixes,
    queue_remediation

# ... implementation of exported functions ...

end
```

---

## Integration Checklist (Week 27)

### Stage 1: Health Monitoring
- [ ] Import SpectralAnalyzer in agent modules
- [ ] Add health check to proof attempt function
- [ ] Log gap state with each attempt
- [ ] Test with 10-20 proof attempts
- [ ] Verify health monitoring overhead < 50ms

### Stage 2: Comprehension Discovery
- [ ] Import SpectralRandomWalk in agent modules
- [ ] Implement comprehension region lookup
- [ ] Add co-visitation-based sampling
- [ ] Test with 50 different theorems
- [ ] Verify comprehension regions found 90%+ of time

### Stage 3: Efficient Navigation
- [ ] Initialize bidirectional index at startup
- [ ] Implement O(1) proof lookup
- [ ] Add LHoTT resource tracking
- [ ] Test cache hit rate
- [ ] Verify navigation < 0.1s per query

### Stage 4: Remediation Detection
- [ ] Import all remediation skills
- [ ] Implement gap drop detection
- [ ] Create remediation suggestion workflow
- [ ] Test with gap degradation scenarios
- [ ] Verify suggestions generate in < 2 seconds

---

## Performance Targets (Week 27-28)

| Operation | Target | Status |
|-----------|--------|--------|
| Health check | < 0.5s | Target |
| Comprehension discovery | < 3s | Target |
| Proof lookup | < 0.1s | Target |
| Proof attempt | Variable | Tracked |
| Remediation suggestion | < 2s | Target |
| Total per attempt | < 10s | Target |

---

## Learning & Feedback Loops

### Agent Learning from Co-visitation

As agents make proof attempts, they should:

1. **Log success patterns** - Which comprehension regions → successful proofs?
2. **Update priors** - Weight theorems from high-success regions higher
3. **Adapt sampling** - Over time, focus on most-productive regions
4. **Share knowledge** - Collectively improve comprehension models

```julia
# Example: Learning from co-visitation success patterns
struct ComprehensionLearning
    theorem_id::Int
    region::Vector{Int}
    success_rate::Float64
    attempts::Int
    last_updated::Float64
end

learning_database = Dict{Int, ComprehensionLearning}()

function update_learning_from_success(theorem_id::Int, region::Vector{Int}, success::Bool)
    key = theorem_id

    if haskey(learning_database, key)
        entry = learning_database[key]
        old_success_rate = entry.success_rate
        new_attempts = entry.attempts + 1
        new_success_rate = (old_success_rate * entry.attempts + (success ? 1 : 0)) / new_attempts

        learning_database[key] = ComprehensionLearning(
            theorem_id,
            region,
            new_success_rate,
            new_attempts,
            time()
        )
    else
        learning_database[key] = ComprehensionLearning(
            theorem_id,
            region,
            success ? 1.0 : 0.0,
            1,
            time()
        )
    end
end
```

---

## Success Metrics (Week 28 Validation)

### Operational Metrics
- [ ] Agents successfully import all 6 skills
- [ ] Health checks < 50ms overhead
- [ ] Comprehension regions found 90%+ of time
- [ ] Proof lookup < 0.1s consistently
- [ ] Remediation suggestions < 2s

### Discovery Metrics
- [ ] Average theorems discovered per query: 5-10
- [ ] Co-visitation success rate: > 60%
- [ ] Comprehension region coverage: > 80%
- [ ] Related theorem relevance: 70%+ rated useful

### Performance Metrics
- [ ] Total proof attempt time: < 10s average
- [ ] System health overhead: < 5% vs baseline
- [ ] Cache hit rate: > 95% (after warm-up)
- [ ] Resource efficiency: Linear consumption tracked

### Remediation Metrics
- [ ] Gap drops detected: 100% within 5 attempts
- [ ] Suggestions generated correctly: 100%
- [ ] Fix applicability: > 80%
- [ ] Time to remediation: < 5 seconds from detection

---

## Potential Issues & Mitigations

### Issue 1: Gap Analysis Too Slow
**Problem**: Full analysis takes > 0.5s, blocks agent
**Mitigation**: Cache analysis results for 10 seconds, only re-compute on change

### Issue 2: Comprehension Regions Missing
**Problem**: Some theorems have no comprehension region
**Mitigation**: Fall back to degree-based ranking if region empty

### Issue 3: Proof Consumption Tracking Overhead
**Problem**: Dict tracking uses memory
**Mitigation**: Implement circular buffer (keep last 1000 proofs)

### Issue 4: Remediation False Positives
**Problem**: Gap drop from random variation, not real problem
**Mitigation**: Require 2 consecutive drops OR > 0.1 difference

---

## Next Phase: Week 28

**Objective**: Deploy Phase 2 to production

### CI/CD Integration
- Generate GitHub Actions workflow
- Deploy per-prover parallel checking
- Set up automated PR comments with gap metrics

### Full Integration Testing
- Test with actual 5,652+ theorem catalog
- Verify all 6 provers coordinate properly
- Measure end-to-end performance
- Validate learning feedback loops

---

## Resources

**Skills Location**: `music-topos/.codex/skills/`
**Framework Guide**: This file
**Code Templates**: See sections above
**Performance Baseline**: SPECTRAL_SKILLS_ECOSYSTEM.md

---

## Status

🔵 **PHASE 2: FRAMEWORK DESIGNED** 🔵

Agent integration framework complete. Ready to implement stages 1-4 during Week 27.

**Next**: Week 27 - Implement Stage 1 Health Monitoring

---

**Generated**: December 22, 2025 23:50 UTC
**Phase**: 2 of 4
**Status**: Prepared & Ready to Execute
