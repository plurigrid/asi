"""
    ProductionDashboard

Production monitoring dashboard for spectral health and prover performance.

Phase 4: Production Integration
===============================

Provides:
- Real-time health status
- Per-prover metrics
- Historical trends
- Alert management
"""

module ProductionDashboard

using Dates
using Statistics

# Note: Dependencies should be loaded by caller
# ProductionConfig, SpectralAgentSkills, HealthTracking

export
    DashboardSnapshot,
    ProverMetrics,
    AlertLevel,
    Alert,
    create_dashboard_snapshot,
    get_prover_metrics,
    check_alerts,
    print_dashboard,
    print_compact_status

# ============================================================================
# Part 1: Data Structures
# ============================================================================

@enum AlertLevel begin
    INFO = 1
    WARNING = 2
    CRITICAL = 3
end

"""
    Alert

A system alert.
"""
struct Alert
    level::AlertLevel
    message::String
    prover::Union{Symbol, Nothing}
    timestamp::Float64
    metric_name::String
    current_value::Float64
    threshold::Float64
end

"""
    ProverMetrics

Metrics for a single prover.
"""
struct ProverMetrics
    name::Symbol
    enabled::Bool
    tasks_completed::Int
    tasks_successful::Int
    success_rate::Float64
    avg_duration_ms::Float64
    current_load::Int
    max_load::Int
    health_gap::Float64
    status::Symbol                        # :healthy, :degraded, :critical, :offline
end

"""
    DashboardSnapshot

A snapshot of the entire system state.
"""
struct DashboardSnapshot
    timestamp::DateTime
    
    # Global health
    overall_gap::Float64
    overall_status::Symbol
    ramanujan_property::Bool
    
    # Prover metrics
    prover_metrics::Vector{ProverMetrics}
    
    # Catalog stats
    total_theorems::Int
    theorems_proven::Int
    proof_coverage::Float64
    
    # Performance
    avg_proof_time_ms::Float64
    proofs_per_minute::Float64
    
    # Alerts
    active_alerts::Vector{Alert}
end

# ============================================================================
# Part 2: Metrics Collection
# ============================================================================

"""
    get_prover_metrics(config, prover_name; stats) -> ProverMetrics

Get metrics for a specific prover.
"""
function get_prover_metrics(
    config,
    prover_name::Symbol;
    tasks_completed::Int=0,
    tasks_successful::Int=0,
    avg_duration_ms::Float64=0.0,
    current_load::Int=0
)::ProverMetrics
    
    prover_config = Main.ProductionConfig.get_prover_config(config, prover_name)
    
    success_rate = tasks_completed > 0 ? tasks_successful / tasks_completed : 1.0
    
    # Get health - simulated gap
    gap = 0.25 + randn() * 0.05
    
    # Determine status
    status = if !prover_config.enabled
        :offline
    elseif gap >= 0.25
        :healthy
    elseif gap >= 0.20
        :degraded
    else
        :critical
    end
    
    return ProverMetrics(
        prover_name,
        prover_config.enabled,
        tasks_completed,
        tasks_successful,
        success_rate,
        avg_duration_ms,
        current_load,
        prover_config.max_parallel,
        gap,
        status
    )
end

"""
    create_dashboard_snapshot(config; orchestration_metrics) -> DashboardSnapshot

Create a snapshot of the current system state.
"""
function create_dashboard_snapshot(
    config;
    theorems_proven::Int=0,
    avg_proof_time_ms::Float64=0.0,
    proofs_per_minute::Float64=0.0
)::DashboardSnapshot
    
    # Get overall health - simulated
    gap = 0.25 + randn() * 0.05
    healthy = gap >= 0.25
    degraded = gap >= 0.20 && gap < 0.25
    severe = gap < 0.20
    
    # Determine overall status
    overall_status = if healthy
        :healthy
    elseif severe
        :critical
    else
        :degraded
    end
    
    # Collect prover metrics
    prover_metrics = ProverMetrics[]
    for prover in Main.ProductionConfig.get_all_provers(config; enabled_only=false)
        metrics = get_prover_metrics(config, prover.name)
        push!(prover_metrics, metrics)
    end
    
    # Calculate coverage
    proof_coverage = config.total_theorems > 0 ? theorems_proven / config.total_theorems : 0.0
    
    # Create a simple health struct for alerts
    health = (gap=gap, healthy=healthy, degraded=degraded, severe=severe)
    
    # Check for alerts
    alerts = check_alerts(config, health, prover_metrics)
    
    return DashboardSnapshot(
        now(),
        gap,
        overall_status,
        gap >= 0.25,
        prover_metrics,
        config.total_theorems,
        theorems_proven,
        proof_coverage,
        avg_proof_time_ms,
        proofs_per_minute,
        alerts
    )
end

# ============================================================================
# Part 3: Alert Checking
# ============================================================================

"""
    check_alerts(config, health, prover_metrics) -> Vector{Alert}

Check for system alerts.
"""
function check_alerts(
    config,
    health,
    prover_metrics::Vector{ProverMetrics}
)::Vector{Alert}
    
    alerts = Alert[]
    
    # Global health alerts
    if health.severe
        push!(alerts, Alert(
            CRITICAL,
            "System health critical - Ramanujan property violated",
            nothing,
            time(),
            "spectral_gap",
            health.gap,
            0.25
        ))
    elseif health.degraded
        push!(alerts, Alert(
            WARNING,
            "System health degraded - approaching threshold",
            nothing,
            time(),
            "spectral_gap",
            health.gap,
            0.25
        ))
    end
    
    # Per-prover alerts
    for metrics in prover_metrics
        if !metrics.enabled
            continue
        end
        
        # Low success rate
        if metrics.tasks_completed >= 10 && metrics.success_rate < 0.7
            push!(alerts, Alert(
                WARNING,
                "Low success rate for $(metrics.name)",
                metrics.name,
                time(),
                "success_rate",
                metrics.success_rate,
                0.7
            ))
        end
        
        # High load
        if metrics.current_load >= metrics.max_load
            push!(alerts, Alert(
                WARNING,
                "Prover $(metrics.name) at maximum load",
                metrics.name,
                time(),
                "load",
                Float64(metrics.current_load),
                Float64(metrics.max_load)
            ))
        end
        
        # Prover-specific health
        if metrics.health_gap < 0.20
            push!(alerts, Alert(
                CRITICAL,
                "Prover $(metrics.name) health critical",
                metrics.name,
                time(),
                "prover_gap",
                metrics.health_gap,
                0.20
            ))
        end
    end
    
    return alerts
end

# ============================================================================
# Part 4: Display Functions
# ============================================================================

"""
    print_dashboard(snapshot)

Print a full dashboard view.
"""
function print_dashboard(snapshot::DashboardSnapshot)
    println()
    println("╔" * "═" ^ 70 * "╗")
    println("║" * " " ^ 20 * "SPECTRAL HEALTH DASHBOARD" * " " ^ 25 * "║")
    println("╠" * "═" ^ 70 * "╣")
    println()
    
    # Timestamp
    println("  📅 $(Dates.format(snapshot.timestamp, "yyyy-mm-dd HH:MM:SS"))")
    println()
    
    # Overall Status
    status_emoji = snapshot.overall_status == :healthy ? "🟢" :
                   snapshot.overall_status == :critical ? "🔴" : "🟡"
    ramanujan_status = snapshot.ramanujan_property ? "✓ Maintained" : "✗ Violated"
    
    println("  ╭─────────────────────────────────────────────────────────────────╮")
    println("  │  OVERALL STATUS                                                 │")
    println("  ├─────────────────────────────────────────────────────────────────┤")
    println("  │  $status_emoji Status: $(uppercase(string(snapshot.overall_status)))")
    println("  │  📊 Spectral Gap: $(round(snapshot.overall_gap, digits=4))")
    println("  │  🔷 Ramanujan Property: $ramanujan_status")
    println("  ╰─────────────────────────────────────────────────────────────────╯")
    println()
    
    # Catalog Progress
    coverage_pct = round(100 * snapshot.proof_coverage, digits=1)
    bar_length = 40
    filled = round(Int, bar_length * snapshot.proof_coverage)
    bar = "█" ^ filled * "░" ^ (bar_length - filled)
    
    println("  ╭─────────────────────────────────────────────────────────────────╮")
    println("  │  CATALOG PROGRESS                                               │")
    println("  ├─────────────────────────────────────────────────────────────────┤")
    println("  │  📚 Theorems: $(snapshot.theorems_proven) / $(snapshot.total_theorems)")
    println("  │  [$bar] $coverage_pct%")
    println("  ╰─────────────────────────────────────────────────────────────────╯")
    println()
    
    # Prover Status
    println("  ╭─────────────────────────────────────────────────────────────────╮")
    println("  │  PROVER STATUS                                                  │")
    println("  ├─────────────────────────────────────────────────────────────────┤")
    
    for metrics in snapshot.prover_metrics
        emoji = metrics.status == :healthy ? "🟢" :
                metrics.status == :critical ? "🔴" :
                metrics.status == :degraded ? "🟡" : "⚫"
        enabled = metrics.enabled ? "" : " (disabled)"
        success = round(100 * metrics.success_rate, digits=0)
        load = "$(metrics.current_load)/$(metrics.max_load)"
        
        println("  │  $emoji $(rpad(string(metrics.name), 12))$enabled")
        println("  │      Success: $(success)%  Load: $load  Gap: $(round(metrics.health_gap, digits=3))")
    end
    
    println("  ╰─────────────────────────────────────────────────────────────────╯")
    println()
    
    # Performance
    println("  ╭─────────────────────────────────────────────────────────────────╮")
    println("  │  PERFORMANCE                                                    │")
    println("  ├─────────────────────────────────────────────────────────────────┤")
    println("  │  ⏱️  Avg Proof Time: $(round(snapshot.avg_proof_time_ms, digits=1))ms")
    println("  │  📈 Proofs/Minute: $(round(snapshot.proofs_per_minute, digits=1))")
    println("  ╰─────────────────────────────────────────────────────────────────╯")
    println()
    
    # Alerts
    if !isempty(snapshot.active_alerts)
        println("  ╭─────────────────────────────────────────────────────────────────╮")
        println("  │  ⚠️  ACTIVE ALERTS ($(length(snapshot.active_alerts)))                                       │")
        println("  ├─────────────────────────────────────────────────────────────────┤")
        
        for alert in snapshot.active_alerts
            level_emoji = alert.level == CRITICAL ? "🔴" :
                          alert.level == WARNING ? "🟡" : "🔵"
            println("  │  $level_emoji $(alert.message)")
        end
        
        println("  ╰─────────────────────────────────────────────────────────────────╯")
    else
        println("  ╭─────────────────────────────────────────────────────────────────╮")
        println("  │  ✅ No active alerts                                            │")
        println("  ╰─────────────────────────────────────────────────────────────────╯")
    end
    
    println()
    println("╚" * "═" ^ 70 * "╝")
    println()
end

"""
    print_compact_status(snapshot)

Print a compact one-line status.
"""
function print_compact_status(snapshot::DashboardSnapshot)
    status_emoji = snapshot.overall_status == :healthy ? "🟢" :
                   snapshot.overall_status == :critical ? "🔴" : "🟡"
    
    enabled_provers = count(m -> m.enabled, snapshot.prover_metrics)
    healthy_provers = count(m -> m.status == :healthy, snapshot.prover_metrics)
    
    alert_count = length(snapshot.active_alerts)
    alert_str = alert_count > 0 ? " ⚠️$alert_count" : ""
    
    println("$status_emoji Gap:$(round(snapshot.overall_gap, digits=3)) | " *
            "Provers:$healthy_provers/$enabled_provers | " *
            "Proven:$(snapshot.theorems_proven)/$(snapshot.total_theorems)$alert_str")
end

end  # module ProductionDashboard
