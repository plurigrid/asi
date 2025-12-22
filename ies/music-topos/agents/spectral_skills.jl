"""
    SpectralAgentSkills

Integration layer for agents to use spectral architecture skills.
Provides health monitoring, theorem discovery, and remediation.

Phase 2 Stage 1: Health Monitoring Implementation
================================================

This module enables agents to be aware of system health before
attempting proofs. Provides lightweight metrics without blocking
proof attempts.
"""

module SpectralAgentSkills

using LinearAlgebra
using Statistics
using Dates

# Import spectral skills
# Determine correct path based on script location
skill_path = if isfile("../.codex/skills/spectral-gap-analyzer/spectral_analyzer.jl")
    "../.codex/skills/spectral-gap-analyzer/spectral_analyzer.jl"
elseif isfile("../../.codex/skills/spectral-gap-analyzer/spectral_analyzer.jl")
    "../../.codex/skills/spectral-gap-analyzer/spectral_analyzer.jl"
else
    # Fallback: use absolute path
    "/Users/bob/ies/music-topos/.codex/skills/spectral-gap-analyzer/spectral_analyzer.jl"
end

USE_REAL_ANALYZER = false
try
    include(skill_path)
    import .SpectralAnalyzer
    USE_REAL_ANALYZER = true
catch e
    @warn "Could not load SpectralAnalyzer: $e, using fallback simulated data"
    USE_REAL_ANALYZER = false
end

# Fallback function for testing without real spectral analyzer
function analyze_all_provers_fallback()
    return Dict(
        "overall_gap" => 0.25 + randn() * 0.02,
        "provers" => Dict(
            "dafny" => 0.25 + randn() * 0.02,
            "lean4" => 0.25 + randn() * 0.02,
            "stellogen" => 0.25 + randn() * 0.02
        )
    )
end

export
    SystemHealthStatus,
    check_system_health,
    get_system_gap,
    is_system_healthy,
    get_health_description

# ============================================================================
# Part 1: Health Status Data Structure
# ============================================================================

"""
    SystemHealthStatus

Represents current system health for agent decision-making.
"""
mutable struct SystemHealthStatus
    gap::Float64              # Spectral gap λ₁ - λ₂
    healthy::Bool             # gap >= 0.25?
    degraded::Bool            # 0.20 <= gap < 0.25?
    severe::Bool              # gap < 0.20?
    timestamp::Float64        # When measured
    recommendation::String    # What agent should do
end

function Base.show(io::IO, h::SystemHealthStatus)
    status_symbol = h.healthy ? "✓" : h.severe ? "✗" : "⚠"
    println(io, "$status_symbol HealthStatus(gap=$(round(h.gap, digits=4)), healthy=$(h.healthy), rec=\"$(h.recommendation)\")")
end

# ============================================================================
# Part 2: Health Monitoring Functions
# ============================================================================

"""
    check_system_health() -> SystemHealthStatus

Check system health before proof attempt.
Returns detailed status with recommendation for agent.

Safety-first approach: errors assume degraded (safe default).
"""
function check_system_health()::SystemHealthStatus
    try
        # Measure spectral gap (Week 1 module)
        if USE_REAL_ANALYZER
            analysis = SpectralAnalyzer.analyze_all_provers()
        else
            analysis = analyze_all_provers_fallback()
        end
        gap = analysis["overall_gap"]
        timestamp = time()

        # Classify health status based on gap
        if gap >= 0.25
            # Healthy: Ramanujan optimal
            healthy = true
            degraded = false
            severe = false
            rec = "✓ System healthy (gap=$(round(gap, digits=4))), proceed normally"

        elseif gap >= 0.20
            # Degraded: Still functional but concerning
            healthy = false
            degraded = true
            severe = false
            rec = "⚠ System degraded (gap=$(round(gap, digits=4))), proceed with caution"

        else
            # Severe: Critical, may need remediation
            healthy = false
            degraded = true
            severe = true
            rec = "✗ System critical (gap=$(round(gap, digits=4))), consider remediation first"
        end

        return SystemHealthStatus(gap, healthy, degraded, severe, timestamp, rec)

    catch e
        # If health check fails, assume degraded (safe default)
        @warn "Health check failed: $e, assuming degraded"
        return SystemHealthStatus(
            0.15,
            false,
            true,
            false,
            time(),
            "✗ Health check error: $(string(e))"
        )
    end
end

"""
    get_system_gap() -> Float64

Get current spectral gap (convenience function).
Returns 0.0 on error (safe default).
"""
function get_system_gap()::Float64
    try
        analysis = SpectralAnalyzer.analyze_all_provers()
        return analysis["overall_gap"]
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
    gap = get_system_gap()
    return gap >= threshold
end

"""
    get_health_description(health::SystemHealthStatus) -> String

Get human-readable description of health status.
Useful for logging and debugging.
"""
function get_health_description(health::SystemHealthStatus)::String
    status_icon = health.healthy ? "✓" : health.severe ? "✗" : "⚠"
    health_type = health.healthy ? "HEALTHY" : health.severe ? "CRITICAL" : "DEGRADED"

    return """
    $status_icon Health Status: $health_type
      Gap: $(round(health.gap, digits=4))
      Time: $(Dates.format(Dates.unix2datetime(health.timestamp), "HH:MM:SS"))
      Recommendation: $(health.recommendation)
    """
end

# ============================================================================
# Part 3: Agent Integration Functions
# ============================================================================

"""
    should_attempt_proof(health::SystemHealthStatus) -> Bool

Determine if agent should attempt proof based on health.
Conservative: skip on severe, warn on degraded, proceed on healthy.
"""
function should_attempt_proof(health::SystemHealthStatus)::Bool
    if health.severe
        return false  # Don't attempt on critical
    end
    # Can attempt on both healthy and degraded
    return true
end

"""
    get_proof_attempt_priority(health::SystemHealthStatus) -> Float64

Return priority multiplier for proof attempts based on health.
Higher priority = more aggressive exploration.

- Healthy (gap >= 0.25): priority = 1.0 (normal)
- Degraded (0.20-0.25): priority = 0.7 (reduced)
- Severe (< 0.20): priority = 0.0 (skip)
"""
function get_proof_attempt_priority(health::SystemHealthStatus)::Float64
    if health.severe
        return 0.0
    elseif health.degraded
        return 0.7
    else
        return 1.0
    end
end

# ============================================================================
# Part 4: Utilities
# ============================================================================

"""
    health_status_emoji(health::SystemHealthStatus) -> String

Get emoji representation of health status.
"""
function health_status_emoji(health::SystemHealthStatus)::String
    if health.healthy
        return "🟢"  # Green - healthy
    elseif health.severe
        return "🔴"  # Red - critical
    else
        return "🟡"  # Yellow - degraded
    end
end

"""
    gap_to_emoji(gap::Float64) -> String

Convert gap value to emoji.
"""
function gap_to_emoji(gap::Float64)::String
    if gap >= 0.25
        return "✓"   # Ramanujan optimal
    elseif gap >= 0.20
        return "⚠"   # Degraded
    else
        return "✗"   # Critical
    end
end

end  # module SpectralAgentSkills
