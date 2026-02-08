"""
Test Phase 4: Production Integration

Tests:
1. Production configuration
2. 6-prover orchestration
3. Production dashboard
4. End-to-end workflow
"""

using Statistics

println("=" ^ 70)
println(" PHASE 4: PRODUCTION INTEGRATION TEST")
println("=" ^ 70)
println()

# ============================================================================
# Load modules
# ============================================================================

println("Loading modules...")

include("production_config.jl")
include("prover_orchestrator.jl")
include("production_dashboard.jl")

using .ProductionConfig
using .ProverOrchestrator
using .ProductionDashboard

println("✓ All modules loaded")
println()

# ============================================================================
# Test 1: Production Configuration
# ============================================================================

println("-" ^ 70)
println(" TEST 1: Production Configuration")
println("-" ^ 70)

config = load_production_config()

println("Configuration loaded:")
println("  Total theorems: $(config.total_theorems)")
println("  Provers configured: $(length(config.provers))")
println("  Enabled provers: $(count(p -> p.enabled, values(config.provers)))")

# Validate
valid, errors = validate_config(config)
if valid
    println("  ✓ Configuration valid")
else
    println("  ✗ Configuration errors: $(errors)")
end

# List provers
println("\nProvers by priority:")
for prover in get_all_provers(config)
    caps = join(string.(prover.capabilities[1:min(3, length(prover.capabilities))]), ", ")
    println("  $(prover.priority). $(prover.name): $(caps)...")
end

test1_pass = valid && length(config.provers) == 6
println("\nTest 1: $(test1_pass ? "✓ PASS" : "✗ FAIL")")
println()

# ============================================================================
# Test 2: Prover Orchestration
# ============================================================================

println("-" ^ 70)
println(" TEST 2: Prover Orchestration")
println("-" ^ 70)

# Create session
session = create_orchestration_session(config)
println("Session created: $(session.session_id)")
println("Initial health gap: $(round(session.health_gap, digits=4))")

# Submit tasks for different theorem types
println("\nSubmitting 20 tasks...")

for i in 1:20
    # Vary capabilities needed
    caps = if i % 3 == 0
        [:dependent_types]
    elseif i % 5 == 0
        [:linear_types]
    else
        Symbol[]
    end
    
    task = submit_task(
        session,
        1000 + i,
        "Theorem_$i",
        "prove: prop_$i",
        required_capabilities=caps
    )
end

println("Tasks submitted: $(length(session.tasks))")

# Check prover distribution
println("\nTask distribution:")
prover_counts = Dict{Symbol, Int}()
for task in session.tasks
    prover_counts[task.assigned_prover] = get(prover_counts, task.assigned_prover, 0) + 1
end
for (prover, count) in sort(collect(prover_counts), by=x->-x[2])
    println("  $(prover): $count tasks")
end

# Execute tasks
println("\nExecuting tasks...")
results = execute_parallel(session, session.tasks)
println("Completed: $(length(results)) tasks")

# Get metrics
metrics = get_orchestration_metrics(session)
println("\nMetrics:")
println("  Success rate: $(round(100 * metrics.successful_tasks / metrics.total_tasks, digits=1))%")
println("  Avg duration: $(round(metrics.avg_duration * 1000, digits=2))ms")
println("  Provers used: $(length(metrics.provers_used))")

test2_pass = length(results) == 20 && metrics.successful_tasks > 0
println("\nTest 2: $(test2_pass ? "✓ PASS" : "✗ FAIL")")
println()

# ============================================================================
# Test 3: Production Dashboard
# ============================================================================

println("-" ^ 70)
println(" TEST 3: Production Dashboard")
println("-" ^ 70)

# Create snapshot
snapshot = create_dashboard_snapshot(
    config,
    theorems_proven=metrics.successful_tasks,
    avg_proof_time_ms=metrics.avg_duration * 1000,
    proofs_per_minute=60.0 / max(0.001, metrics.total_duration) * metrics.total_tasks
)

println("Dashboard snapshot created:")
println("  Timestamp: $(snapshot.timestamp)")
println("  Overall status: $(snapshot.overall_status)")
println("  Ramanujan property: $(snapshot.ramanujan_property)")
println("  Active alerts: $(length(snapshot.active_alerts))")

# Print compact status
print("  Compact: ")
print_compact_status(snapshot)

test3_pass = snapshot.overall_gap > 0 && !isempty(snapshot.prover_metrics)
println("\nTest 3: $(test3_pass ? "✓ PASS" : "✗ FAIL")")
println()

# ============================================================================
# Test 4: End-to-End Workflow
# ============================================================================

println("-" ^ 70)
println(" TEST 4: End-to-End Workflow")
println("-" ^ 70)

println("Simulating production workflow...")

# Step 1: Load config
workflow_config = load_production_config()
println("  1. ✓ Configuration loaded")

# Step 2: Create orchestration session
workflow_session = create_orchestration_session(workflow_config)
println("  2. ✓ Orchestration session created")

# Step 3: Submit batch of theorems
batch_size = 50
for i in 1:batch_size
    submit_task(workflow_session, 2000 + i, "BatchTheorem_$i", "prove: batch_$i")
end
println("  3. ✓ Submitted $batch_size theorems")

# Step 4: Execute with health monitoring
execute_parallel(workflow_session, workflow_session.tasks)
println("  4. ✓ Executed all tasks")

# Step 5: Check dashboard
final_metrics = get_orchestration_metrics(workflow_session)
final_snapshot = create_dashboard_snapshot(
    workflow_config,
    theorems_proven=final_metrics.successful_tasks
)
println("  5. ✓ Dashboard updated")

# Step 6: Verify health maintained
health_maintained = final_snapshot.overall_gap >= 0.20
println("  6. $(health_maintained ? "✓" : "⚠") Health gap: $(round(final_snapshot.overall_gap, digits=4))")

# Step 7: Check for critical alerts
critical_alerts = filter(a -> a.level == ProductionDashboard.CRITICAL, final_snapshot.active_alerts)
no_critical = isempty(critical_alerts)
println("  7. $(no_critical ? "✓" : "⚠") Critical alerts: $(length(critical_alerts))")

test4_pass = final_metrics.successful_tasks > 0 && health_maintained
println("\nTest 4: $(test4_pass ? "✓ PASS" : "✗ FAIL")")
println()

# ============================================================================
# Test 5: Performance Benchmark
# ============================================================================

println("-" ^ 70)
println(" TEST 5: Performance Benchmark")
println("-" ^ 70)

# Benchmark configuration loading
config_times = Float64[]
for _ in 1:10
    t0 = time()
    load_production_config()
    push!(config_times, time() - t0)
end
println("Config loading: $(round(mean(config_times) * 1000, digits=2))ms avg")

# Benchmark session creation
session_times = Float64[]
for _ in 1:10
    t0 = time()
    create_orchestration_session(config)
    push!(session_times, time() - t0)
end
println("Session creation: $(round(mean(session_times) * 1000, digits=2))ms avg")

# Benchmark task submission
submit_times = Float64[]
test_session = create_orchestration_session(config)
for i in 1:100
    t0 = time()
    submit_task(test_session, 3000 + i, "PerfTest_$i", "prove: perf_$i")
    push!(submit_times, time() - t0)
end
println("Task submission: $(round(mean(submit_times) * 1000, digits=3))ms avg")

# Benchmark dashboard
dash_times = Float64[]
for _ in 1:10
    t0 = time()
    create_dashboard_snapshot(config)
    push!(dash_times, time() - t0)
end
println("Dashboard snapshot: $(round(mean(dash_times) * 1000, digits=2))ms avg")

test5_pass = mean(config_times) < 0.1 && mean(dash_times) < 0.1
println("\nTest 5: $(test5_pass ? "✓ PASS" : "✗ FAIL")")
println()

# ============================================================================
# Summary
# ============================================================================

println("=" ^ 70)
println(" PHASE 4 TEST RESULTS")
println("=" ^ 70)
println()

all_tests = [test1_pass, test2_pass, test3_pass, test4_pass, test5_pass]
test_names = [
    "Production Configuration",
    "Prover Orchestration",
    "Production Dashboard",
    "End-to-End Workflow",
    "Performance Benchmark"
]

for (name, passed) in zip(test_names, all_tests)
    status = passed ? "✓ PASS" : "✗ FAIL"
    println("  $status  $name")
end

println()
passed_count = sum(all_tests)
total_count = length(all_tests)

if all(all_tests)
    println("=" ^ 70)
    println(" 🎉 ALL PHASE 4 TESTS PASSED ($passed_count/$total_count)")
    println(" Production integration ready for deployment!")
    println("=" ^ 70)
else
    println("=" ^ 70)
    println(" ⚠️  SOME TESTS FAILED ($passed_count/$total_count passed)")
    println("=" ^ 70)
end
println()

# Print full dashboard at end
println("\n" * "-" ^ 70)
println(" FINAL DASHBOARD VIEW")
println("-" ^ 70)
print_dashboard(final_snapshot)
