# Phase 2 Stage 1: Health Monitoring - Quick Start

**Date**: December 22, 2025
**Phase**: 2 of 4
**Stage**: 1 of 4 (Health Monitoring)
**Duration**: Week 27.1 (3-5 days)
**Status**: 🟢 READY TO IMPLEMENT

---

## What You're Building

A lightweight health monitoring layer that agents check before attempting proofs. Provides system state awareness without blocking proof attempts.

---

## Step 1: Create Agent Skills Module (15 minutes)

Create new file: `music-topos/agents/spectral_skills.jl`

```julia
"""
    SpectralAgentSkills

Integration layer for agents to use spectral architecture skills.
Provides health monitoring, theorem discovery, and remediation.
"""
module SpectralAgentSkills

using LinearAlgebra
using Statistics

# Import spectral skills from .codex/skills/
include("../../.codex/skills/spectral-gap-analyzer/spectral_analyzer.jl")
include("../../.codex/skills/spectral-random-walker/spectral_random_walk.jl")
include("../../.codex/skills/bidirectional-navigator/bidirectional_index.jl")

import .SpectralAnalyzer
import .SpectralRandomWalk
import .BidirectionalIndex

export check_system_health, get_system_gap, is_system_healthy

# ============================================================================
# STAGE 1: Health Monitoring
# ============================================================================

"""
    SystemHealthStatus

Represents current system health for agent decision-making.
"""
mutable struct SystemHealthStatus
    gap::Float64
    healthy::Bool
    degraded::Bool
    severe::Bool
    timestamp::Float64
    recommendation::String
end

"""
    check_system_health() -> SystemHealthStatus

Check system health before proof attempt.
Returns status with recommendation for agent.
"""
function check_system_health()::SystemHealthStatus
    try
        # Measure spectral gap
        gap = SpectralAnalyzer.analyze_all_provers()["overall_gap"]
        timestamp = time()

        # Classify health status
        if gap >= 0.25
            healthy = true
            degraded = false
            severe = false
            rec = "✓ System healthy (gap=$gap), proceed normally"
        elseif gap >= 0.20
            healthy = false
            degraded = true
            severe = false
            rec = "⚠ System degraded (gap=$gap), proceed with caution"
        else
            healthy = false
            degraded = true
            severe = true
            rec = "✗ System critically degraded (gap=$gap), consider remediation first"
        end

        return SystemHealthStatus(gap, healthy, degraded, severe, timestamp, rec)

    catch e
        # If health check fails, assume degraded (safe default)
        @warn "Health check failed: $e, assuming degraded"
        return SystemHealthStatus(0.15, false, true, false, time(), "✗ Health check error: $e")
    end
end

"""
    get_system_gap() -> Float64

Get current spectral gap (convenience function).
"""
function get_system_gap()::Float64
    try
        return SpectralAnalyzer.analyze_all_provers()["overall_gap"]
    catch e
        @warn "Gap measurement failed: $e"
        return 0.0
    end
end

"""
    is_system_healthy(; threshold=0.25) -> Bool

Quick check if system is above health threshold.
"""
function is_system_healthy(; threshold=0.25)::Bool
    return get_system_gap() >= threshold
end

end  # module SpectralAgentSkills
```

---

## Step 2: Integrate into Agent Proof Attempt (10 minutes)

Add to agent's proof attempt function:

```julia
using SpectralAgentSkills

@agent function attempt_proof(theorem_id::Int, goal::String, timeout::Float64=30.0) -> Bool
    """
    Attempt to prove a theorem with health monitoring.
    """

    # STAGE 1: HEALTH CHECK
    start_time = time()
    health = SpectralAgentSkills.check_system_health()

    @info "Health Check: $(health.recommendation)"
    @info "Gap measure: $(round(health.gap, digits=4))"

    # Log health status
    log_proof_attempt(theorem_id, :health_check, health.gap, health.recommendation)

    # Decide whether to proceed
    if health.severe
        @warn "System severely degraded, skipping proof attempt"
        log_proof_attempt(theorem_id, :skipped_degraded, health.gap, "System too degraded")
        return false
    end

    # Continue with proof attempt (stage 2+)
    attempt_start = time()
    success = false

    try
        # ... existing proof attempt logic ...
        # Try proof strategies here
        # ...
        success = true

    catch e
        @error "Proof attempt failed: $e"
        success = false

    finally
        # MEASURE HEALTH AFTER ATTEMPT
        attempt_time = time() - attempt_start
        health_after = SpectralAgentSkills.check_system_health()

        # Log result with health context
        gap_change = health_after.gap - health.gap
        log_proof_attempt(
            theorem_id,
            success ? :success : :failure,
            health_after.gap,
            "Attempt took $(round(attempt_time, digits=2))s, gap change: $(round(gap_change, digits=4))"
        )

        # Alert if gap degraded significantly
        if gap_change < -0.05
            @warn "Gap degraded by $(abs(gap_change)): may need remediation"
        end
    end

    return success
end
```

---

## Step 3: Add Health Tracking (10 minutes)

Create health tracking database:

```julia
# File: music-topos/agents/health_tracking.jl

using DataFrames
using Dates

"""
Health tracking database for agent decisions.
Records gap state at each proof attempt.
"""

mutable struct HealthRecord
    attempt_number::Int
    theorem_id::Int
    timestamp::Float64
    gap_before::Float64
    gap_after::Float64
    success::Bool
    proof_time::Float64
    notes::String
end

# Global tracking (thread-safe)
const HEALTH_RECORDS = HealthRecord[]
const HEALTH_LOCK = ReentrantLock()

"""
    log_proof_attempt(theorem_id, status, gap, notes)

Log a proof attempt with health context.
"""
function log_proof_attempt(
    theorem_id::Int,
    status::Symbol,
    gap::Float64,
    notes::String
)
    lock(HEALTH_LOCK) do
        push!(HEALTH_RECORDS, HealthRecord(
            length(HEALTH_RECORDS) + 1,
            theorem_id,
            time(),
            gap,
            gap,  # Will be updated after attempt
            status === :success,
            0.0,
            notes
        ))
    end
end

"""
    get_health_summary() -> Dict

Get summary statistics of health tracking.
"""
function get_health_summary()::Dict
    lock(HEALTH_LOCK) do
        if isempty(HEALTH_RECORDS)
            return Dict(
                :total_attempts => 0,
                :average_gap => 0.0,
                :healthy_attempts => 0,
                :degraded_attempts => 0
            )
        end

        gaps = [r.gap_before for r in HEALTH_RECORDS]
        healthy = sum(g >= 0.25 for g in gaps)
        degraded = length(gaps) - healthy

        return Dict(
            :total_attempts => length(HEALTH_RECORDS),
            :average_gap => mean(gaps),
            :min_gap => minimum(gaps),
            :max_gap => maximum(gaps),
            :healthy_attempts => healthy,
            :degraded_attempts => degraded,
            :health_percentage => round(100 * healthy / length(gaps), digits=1),
            :latest_gap => gaps[end]
        )
    end
end
```

---

## Step 4: Test Health Monitoring (15 minutes)

Create test script: `test_health_monitoring.jl`

```julia
using Dates

# Test health check function
println("=" ^ 60)
println("SPECTRAL HEALTH MONITORING - TEST")
println("=" ^ 60)

include("music-topos/agents/spectral_skills.jl")
include("music-topos/agents/health_tracking.jl")

using Main.SpectralAgentSkills
using Main

# Test 1: Basic health check
println("\nTest 1: Basic Health Check")
println("-" ^ 40)

for i in 1:3
    println("\nAttempt $i:")
    health = SpectralAgentSkills.check_system_health()
    println("  Gap: $(round(health.gap, digits=4))")
    println("  Healthy: $(health.healthy)")
    println("  Recommendation: $(health.recommendation)")
    println("  Time: $(Dates.format(now(), "HH:MM:SS"))")

    # Log it
    log_proof_attempt(100 + i, :test, health.gap, "Test attempt")

    sleep(0.5)
end

# Test 2: Health summary
println("\n\nTest 2: Health Summary")
println("-" ^ 40)

summary = get_health_summary()
for (key, val) in summary
    println("  $key: $val")
end

# Test 3: Performance
println("\n\nTest 3: Performance Benchmark")
println("-" ^ 40)

times = Float64[]
for i in 1:10
    t0 = time()
    SpectralAgentSkills.check_system_health()
    push!(times, time() - t0)
end

println("  10 health checks:")
println("  - Average: $(round(mean(times)*1000, digits=2))ms")
println("  - Min: $(round(minimum(times)*1000, digits=2))ms")
println("  - Max: $(round(maximum(times)*1000, digits=2))ms")
println("  - Total: $(round(sum(times), digits=3))s")

# Test 4: Gap monitoring
println("\n\nTest 4: Gap Trending")
println("-" ^ 40)

gaps = [SpectralAgentSkills.get_system_gap() for _ in 1:5]
println("  Gap samples: $(map(x -> round(x, digits=4), gaps))")
println("  Average: $(round(mean(gaps), digits=4))")
println("  Stable: $(maximum(gaps) - minimum(gaps) < 0.01 ? "YES" : "NO")")

println("\n" * "=" ^ 60)
println("✅ Health monitoring tests complete")
println("=" ^ 60)
```

Run with:
```bash
julia test_health_monitoring.jl
```

Expected output:
```
============================================================
SPECTRAL HEALTH MONITORING - TEST
============================================================

Test 1: Basic Health Check
----------------------------------------

Attempt 1:
  Gap: 1.6667
  Healthy: true
  Recommendation: ✓ System healthy (gap=1.6667), proceed normally
  Time: 23:45:32

...

Test 2: Health Summary
----------------------------------------
  total_attempts: 3
  average_gap: 1.6667
  healthy_attempts: 3
  degraded_attempts: 0
  health_percentage: 100.0
  latest_gap: 1.6667

Test 3: Performance Benchmark
----------------------------------------
  10 health checks:
  - Average: 45.23ms
  - Min: 42.15ms
  - Max: 52.89ms
  - Total: 0.452s

✅ Health monitoring tests complete
```

---

## Step 5: Integrate into Agent Loop (10 minutes)

Add to main agent execution loop:

```julia
# In agent's main loop:
for iteration in 1:max_iterations
    # Get next theorem to prove
    theorem = get_next_theorem()

    # HEALTH CHECK BEFORE ATTEMPT
    health = SpectralAgentSkills.check_system_health()

    if health.severe
        @info "Iteration $iteration: Skipping (system degraded)"
        continue
    end

    # Attempt proof
    @info "Iteration $iteration: Attempting $(theorem.name) (gap=$(round(health.gap, digits=4)))"

    success = attempt_proof(theorem.id, theorem.goal)

    if success
        @info "  ✓ Success"
        successful_proofs += 1
    else
        @info "  ✗ Failed"
    end

    # Every 10 iterations, log summary
    if iteration % 10 == 0
        summary = get_health_summary()
        @info "Summary after $iteration attempts: $(summary[:average_gap]) gap, $(summary[:health_percentage])% healthy"
    end
end
```

---

## Success Criteria for Stage 1

- [ ] Health monitoring module created (10 lines code/documentation per metric)
- [ ] Health check < 50ms per call (measured in test)
- [ ] 3+ test proof attempts with health logging
- [ ] Gap logged before/after each attempt
- [ ] Health summary reporting working
- [ ] No overhead to agent proof attempts

---

## Expected Results

After completing Stage 1:

```
✅ Agents aware of system state
✅ Gap metric tracked per proof attempt
✅ Health check < 50ms overhead
✅ Patterns showing gap → success correlation emerge
✅ Ready for Stage 2 (Comprehension Discovery)
```

---

## Metrics to Collect

During Stage 1 testing, collect:

1. **Health Check Performance**
   - Average time per check: Target < 50ms
   - Distribution (min/max/stddev)

2. **Gap Statistics**
   - Average gap across attempts
   - Gap stability (variance)
   - Min/max observed

3. **Attempt Outcomes**
   - Proof success rate vs gap
   - Attempts in healthy state
   - Attempts in degraded state

4. **Feedback Loop**
   - Did agents skip proof attempts?
   - Did agents adjust strategy on warnings?
   - Did gap correlate with success?

---

## Files to Create

```
music-topos/agents/
├── spectral_skills.jl          ← Main health monitoring module
├── health_tracking.jl          ← Health database
├── test_health_monitoring.jl   ← Test script
└── agent_integration.jl        ← (Next: Stage 2)
```

---

## Next After Stage 1

Once health monitoring is working:

1. **Measure baseline** - Run 20-50 proof attempts with health tracking
2. **Collect metrics** - Record gap and success patterns
3. **Analyze results** - Identify gap → success correlation
4. **Document findings** - Add to Phase 2 report
5. **Proceed to Stage 2** - Comprehension-guided discovery

---

## Troubleshooting

### Issue: Health check takes > 100ms
**Solution**: Cache results for 10 seconds, only re-compute on change

### Issue: Can't import spectral skills
**Solution**: Check paths, ensure `include()` statements match your file structure

### Issue: Gap always returns 0
**Solution**: Verify SpectralAnalyzer is loading correctly, check adjacency matrix

### Issue: Test script fails
**Solution**: Start with simpler test, just call `check_system_health()` directly

---

## Resources

- **Framework**: PHASE_2_AGENT_INTEGRATION_FRAMEWORK.md
- **Project Status**: SPECTRAL_ARCHITECTURE_PROJECT_STATUS.md
- **Skills Reference**: SPECTRAL_SKILLS_ECOSYSTEM.md

---

**Status**: 🟢 Ready to implement
**Estimated Duration**: 1-2 hours
**Difficulty**: Easy-Medium
**Next Step**: Stage 2 Comprehension Discovery (Week 27.2)

🎉 **Let's get agents healthy!** 🎉
