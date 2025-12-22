"""
    HealthTracking

Database for tracking proof attempts with health context.
Enables learning from system state correlations.

Phase 2 Stage 1: Health Tracking Implementation
"""

module HealthTracking

using Dates
using Statistics

export HealthRecord, log_proof_attempt, get_health_summary, get_attempt_history

# ============================================================================
# Part 1: Data Structures
# ============================================================================

"""
    HealthRecord

Records a single proof attempt with health context.
"""
mutable struct HealthRecord
    attempt_number::Int       # Sequential attempt ID
    theorem_id::Int           # Theorem being proven
    status::Symbol            # :health_check, :skipped, :success, :failure
    gap_before::Float64       # Gap before attempt
    gap_after::Float64        # Gap after attempt
    timestamp::Float64        # When logged
    attempt_duration::Float64 # How long attempt took (seconds)
    notes::String             # Additional notes
end

function Base.show(io::IO, r::HealthRecord)
    gap_change = r.gap_after - r.gap_before
    gap_str = gap_change >= 0 ? "+$(round(gap_change, digits=4))" : "$(round(gap_change, digits=4))"
    println(io, "#$(r.attempt_number) T$(r.theorem_id) $(r.status): gap=$(round(r.gap_before, digits=4))→$(round(r.gap_after, digits=4)) ($gap_str)")
end

# ============================================================================
# Part 2: Global State (Thread-Safe)
# ============================================================================

# Thread-safe record storage
const HEALTH_RECORDS = HealthRecord[]
const HEALTH_LOCK = ReentrantLock()

"""
    log_proof_attempt(theorem_id::Int, status::Symbol, gap::Float64, notes::String="")

Log a proof attempt with health context.
Thread-safe storage using lock.
"""
function log_proof_attempt(
    theorem_id::Int,
    status::Symbol,
    gap::Float64,
    notes::String=""
)
    lock(HEALTH_LOCK) do
        push!(HEALTH_RECORDS, HealthRecord(
            length(HEALTH_RECORDS) + 1,
            theorem_id,
            status,
            gap,
            gap,
            time(),
            0.0,
            notes
        ))
    end
end

"""
    update_attempt_result(attempt_num::Int, gap_after::Float64, duration::Float64)

Update an attempt record with results after completion.
"""
function update_attempt_result(attempt_num::Int, gap_after::Float64, duration::Float64)
    lock(HEALTH_LOCK) do
        if attempt_num <= length(HEALTH_RECORDS)
            HEALTH_RECORDS[attempt_num].gap_after = gap_after
            HEALTH_RECORDS[attempt_num].attempt_duration = duration
        end
    end
end

# ============================================================================
# Part 3: Analysis Functions
# ============================================================================

"""
    get_health_summary() -> Dict

Get summary statistics of health tracking.
Computed on-demand from all records.
"""
function get_health_summary()::Dict
    lock(HEALTH_LOCK) do
        if isempty(HEALTH_RECORDS)
            return Dict(
                :total_attempts => 0,
                :average_gap => 0.0,
                :healthy_attempts => 0,
                :degraded_attempts => 0,
                :successful_attempts => 0,
                :failed_attempts => 0,
                :average_duration => 0.0
            )
        end

        # Extract metrics
        gaps_before = [r.gap_before for r in HEALTH_RECORDS]
        gaps_after = [r.gap_after for r in HEALTH_RECORDS]
        durations = [r.attempt_duration for r in HEALTH_RECORDS]
        success_count = sum(r.status === :success for r in HEALTH_RECORDS)
        failure_count = sum(r.status === :failure for r in HEALTH_RECORDS)
        healthy_count = sum(g >= 0.25 for g in gaps_before)
        degraded_count = sum(0.20 <= g < 0.25 for g in gaps_before)

        # Calculate statistics
        gap_changes = gaps_after - gaps_before
        gap_improved = sum(g > 0.01 for g in gap_changes)
        gap_degraded = sum(g < -0.01 for g in gap_changes)

        return Dict(
            :total_attempts => length(HEALTH_RECORDS),
            :average_gap_before => round(mean(gaps_before), digits=4),
            :average_gap_after => round(mean(gaps_after), digits=4),
            :min_gap => round(minimum(gaps_before), digits=4),
            :max_gap => round(maximum(gaps_before), digits=4),
            :healthy_attempts => healthy_count,
            :degraded_attempts => degraded_count,
            :health_percentage => round(100 * healthy_count / length(HEALTH_RECORDS), digits=1),
            :successful_attempts => success_count,
            :failed_attempts => failure_count,
            :success_rate => length(HEALTH_RECORDS) > 0 ? round(100 * success_count / length(HEALTH_RECORDS), digits=1) : 0.0,
            :gaps_improved => gap_improved,
            :gaps_degraded => gap_degraded,
            :latest_gap => gaps_before[end],
            :average_duration => round(mean(durations[durations .> 0]), digits=3)
        )
    end
end

"""
    get_attempt_history(limit::Int=10) -> Vector{HealthRecord}

Get most recent attempts (default last 10).
"""
function get_attempt_history(limit::Int=10)::Vector{HealthRecord}
    lock(HEALTH_LOCK) do
        if isempty(HEALTH_RECORDS)
            return HealthRecord[]
        end
        start_idx = max(1, length(HEALTH_RECORDS) - limit + 1)
        return HEALTH_RECORDS[start_idx:end]
    end
end

"""
    clear_history()

Clear all recorded attempts (for testing/reset).
"""
function clear_history()
    lock(HEALTH_LOCK) do
        empty!(HEALTH_RECORDS)
    end
end

"""
    get_record_count() -> Int

Get total number of records.
"""
function get_record_count()::Int
    lock(HEALTH_LOCK) do
        return length(HEALTH_RECORDS)
    end
end

# ============================================================================
# Part 4: Reporting Functions
# ============================================================================

"""
    print_summary()

Print human-readable summary of all attempts.
"""
function print_summary()
    summary = get_health_summary()

    println("\n" * "="^60)
    println("HEALTH TRACKING SUMMARY")
    println("="^60)

    println("\nAttempt Statistics:")
    println("  Total attempts:       $(summary[:total_attempts])")
    println("  Successful:           $(summary[:successful_attempts])")
    println("  Failed:               $(summary[:failed_attempts])")
    println("  Success rate:         $(summary[:success_rate])%")

    println("\nHealth Status:")
    println("  Healthy attempts:     $(summary[:healthy_attempts])")
    println("  Degraded attempts:    $(summary[:degraded_attempts])")
    println("  Health percentage:    $(summary[:health_percentage])%")

    println("\nGap Statistics:")
    println("  Average gap (before): $(summary[:average_gap_before])")
    println("  Average gap (after):  $(summary[:average_gap_after])")
    println("  Min gap:              $(summary[:min_gap])")
    println("  Max gap:              $(summary[:max_gap])")
    println("  Latest gap:           $(summary[:latest_gap])")

    println("\nGap Trends:")
    println("  Improved:             $(summary[:gaps_improved])")
    println("  Degraded:             $(summary[:gaps_degraded])")

    println("\nPerformance:")
    println("  Avg attempt duration: $(summary[:average_duration])s")

    println("\n" * "="^60)
end

"""
    print_recent_history(n::Int=10)

Print recent attempts in readable format.
"""
function print_recent_history(n::Int=10)
    history = get_attempt_history(n)

    if isempty(history)
        println("No attempts recorded yet.")
        return
    end

    println("\n" * "="^60)
    println("RECENT ATTEMPT HISTORY (last $n)")
    println("="^60)

    for record in history
        gap_change = record.gap_after - record.gap_before
        gap_str = gap_change >= 0 ? "$(gap_change >= 0 ? "+" : "")$(round(gap_change, digits=4))" : "$(round(gap_change, digits=4))"
        status_emoji = record.status === :success ? "✓" : record.status === :failure ? "✗" : "⚠"

        println("#$(record.attempt_number) $status_emoji T$(record.theorem_id): gap=$(round(record.gap_before, digits=4))→$(round(record.gap_after, digits=4)) ($gap_str)")
    end

    println("="^60)
end

end  # module HealthTracking
