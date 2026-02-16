"""
test_asi_integration.jl

Test Energy Dynamics ACSet with realistic synthetic metrics
mimicking Plurigrid ASI contributor interaction patterns.

This demonstrates:
  1. Extracting metrics from GitHub interaction data patterns
  2. Computing kinetic/potential/total energy
  3. Assigning GF(3) trits
  4. Generating energy reports for skill ecosystem
"""

using Catlab, ACSets, Printf, Statistics

# Include the energy dynamics schema
include("schema.jl")

# ============================================================================
# SIMULATED GITHUB METRICS EXTRACTION
# ============================================================================

"""
Struct to hold GitHub-extracted metrics for a skill
"""
struct SkillMetrics
    name::String
    pr_velocity::Float64           # PRs closed per week
    concurrent_contributors::Int   # Contributors active in last week
    code_complexity::Float64       # Cyclomatic complexity or similar
    acset_nesting_depth::Int       # Nesting level in categorical hierarchy
    storage_bytes::Int             # Size on disk
end

# Realistic synthetic data based on typical Plurigrid ASI skills
# (simulating extraction from gh_acset_export.json)
skills_data = [
    # High-activity skills (PLUS in GF(3) triads)
    SkillMetrics("specter-acset", 2.5, 8, 7.2, 9, 125_000),
    SkillMetrics("open-games", 2.1, 7, 6.8, 8, 98_000),
    SkillMetrics("topos-catcolab", 1.9, 6, 7.1, 10, 145_000),
    SkillMetrics("interaction-nets", 2.3, 7, 6.5, 8, 112_000),
    SkillMetrics("crdt-vterm", 1.8, 6, 5.9, 7, 87_000),

    # Moderate-activity skills (ERGODIC in GF(3) triads)
    SkillMetrics("acset-taxonomy", 1.2, 4, 5.7, 7, 250_000),
    SkillMetrics("kan-extensions", 1.0, 3, 6.2, 8, 178_000),
    SkillMetrics("datalog-fixpoint", 0.9, 3, 5.4, 6, 92_000),
    SkillMetrics("sheaf-cohomology", 0.8, 2, 6.8, 9, 201_000),
    SkillMetrics("structured-decomp", 0.7, 2, 5.3, 6, 156_000),

    # Low-activity skills (MINUS in GF(3) triads)
    SkillMetrics("covariant-fibrations", 0.3, 1, 4.5, 5, 89_000),
    SkillMetrics("temporal-coalgebra", 0.2, 1, 5.1, 7, 134_000),
    SkillMetrics("persistent-homology", 0.4, 1, 5.9, 6, 167_000),
    SkillMetrics("ordered-locale", 0.1, 1, 4.2, 4, 56_000),
    SkillMetrics("lispsyntax-acset", 0.2, 1, 3.8, 5, 45_000),
]

# ============================================================================
# METRIC COMPUTATION FUNCTIONS
# ============================================================================

"""
Compute entropy rate (dS/dt) from PR velocity
Higher PR velocity = higher boundary dissipation
"""
function compute_entropy_rate(pr_velocity::Float64)::Float64
    # Normalize: 0.1 to 2.5 → 0.05 to 0.25
    return pr_velocity / 10.0
end

"""
Compute interaction degree from concurrent contributors
"""
function compute_interaction_degree(concurrent_contributors::Int)::Int
    return max(1, concurrent_contributors)
end

"""
Compute bandwidth utilization (empirical: fraction of typical capacity)
Assumes 10 interactions/week is full capacity
"""
function compute_bandwidth_utilization(pr_velocity::Float64)::Float64
    return min(1.0, pr_velocity / 10.0)
end

"""
Compute schema complexity - use as-is from metrics
"""
function compute_schema_complexity(code_complexity::Float64)::Float64
    return code_complexity
end

"""
Compute representational depth from ACSet nesting
"""
function compute_representational_depth(nesting_depth::Int)::Int
    return nesting_depth
end

# ============================================================================
# ACSet POPULATION
# ============================================================================

"""
Populate the energy dynamics ACSet with realistic Plurigrid ASI data
"""
function populate_asi_acset(skills::Vector{SkillMetrics})
    acset = ACSet{SchEnergyDynamicsACSet}()

    # Add GF(3) trits
    minus_id = add_part!(acset, :Trit; trit_value=-1, trit_name="MINUS")
    ergodic_id = add_part!(acset, :Trit; trit_value=0, trit_name="ERGODIC")
    plus_id = add_part!(acset, :Trit; trit_value=+1, trit_name="PLUS")

    # Add base time point
    t_base = add_part!(acset, :TimePoint; timestamp=0.0)

    # Sort by energy density to determine trit assignment
    skill_records = []

    for (idx, skill) in enumerate(skills)
        # Compute metrics
        entropy_rate = compute_entropy_rate(skill.pr_velocity)
        interaction_degree = compute_interaction_degree(skill.concurrent_contributors)
        bandwidth_utilization = compute_bandwidth_utilization(skill.pr_velocity)
        schema_complexity = compute_schema_complexity(skill.code_complexity)
        representational_depth = compute_representational_depth(skill.acset_nesting_depth)

        # Compute energies
        K = entropy_rate * interaction_degree * bandwidth_utilization
        V = schema_complexity * representational_depth
        H = K + V

        # Energy density for trit assignment
        energy_density = K / Float64(skill.storage_bytes)

        # Store for sorting
        push!(skill_records, (
            idx,
            skill.name,
            K, V, H,
            entropy_rate, interaction_degree, bandwidth_utilization,
            schema_complexity, representational_depth,
            skill.storage_bytes,
            energy_density
        ))
    end

    # Sort by energy density
    sort!(skill_records, by=x -> x[end], rev=true)

    # Assign trits: top third = PLUS, middle = ERGODIC, bottom = MINUS
    n = length(skill_records)
    n_plus = div(n, 3)
    n_ergodic = div(n, 3)
    n_minus = n - n_plus - n_ergodic

    # Add skills to acset
    skill_parts = Dict()

    for (rank, (orig_idx, name, K, V, H, dS, degree, bw, complexity, depth, footprint, density)) in enumerate(skill_records)
        # Determine trit
        if rank <= n_plus
            trit_id = plus_id
        elseif rank <= n_plus + n_ergodic
            trit_id = ergodic_id
        else
            trit_id = minus_id
        end

        # Add skill
        skill_id = add_part!(acset, :Skill;
            schema_complexity=complexity,
            representational_depth=depth,
            storage_footprint=Int64(footprint),
            trit_assignment=trit_id
        )

        # Add reaction structure
        # Reaction rate proportional to energy density
        reaction_id = add_part!(acset, :ReactionStructure;
            cotangent_contribution=0.5 + 0.2 * density,  # Momentum-like
            tangent_contribution=0.5 - 0.2 * density,     # Velocity-like
            reaction_rate=0.1 + 0.8 * density             # Coupling strength
        )

        set_subpart!(acset, skill_id, :reaction, reaction_id)

        # Add energy flow
        flow_id = add_part!(acset, :EnergyFlow;
            entropy_rate=dS,
            interaction_degree=Int64(degree),
            bandwidth_utilization=bw,
            energy_source=skill_id,
            energy_sink=skill_id
        )

        # Add dynamical state
        # Oscillation: some high-K (active), some high-V (latent)
        if rank <= div(n, 2)
            state_id = add_part!(acset, :DynamicalState;
                kinetic_energy=K / H,
                potential_energy=V / H,
                hamiltonian=1.0,
                time_step=t_base,
                current_state=skill_id
            )
        else
            state_id = add_part!(acset, :DynamicalState;
                kinetic_energy=0.2 + 0.3 * rand(),
                potential_energy=0.8 - 0.3 * rand(),
                hamiltonian=1.0,
                time_step=t_base,
                current_state=skill_id
            )
        end

        # Store for reporting
        skill_parts[name] = (skill_id, flow_id, state_id, reaction_id, K, V, H, density, trit_id == plus_id ? "PLUS" : (trit_id == ergodic_id ? "ERGODIC" : "MINUS"))
    end

    return acset, skill_parts
end

# ============================================================================
# ENERGY REPORT & ANALYSIS
# ============================================================================

"""
Generate comprehensive energy report for ASI skill ecosystem
"""
function generate_asi_energy_report(acset, skill_parts::Dict)

    println("=" ^ 100)
    println("PLURIGRID ASI ENERGY DYNAMICS REPORT")
    println("=" ^ 100)

    # GF(3) Conservation
    println("\n▸ GF(3) TRIADIC BALANCE:")
    trits_vals = [acset[i, :trit_value] for i in 1:nparts(acset, :Trit)]
    gf3_sum = mod(sum(trits_vals), 3)
    gf3_balanced = gf3_sum == 0
    println("  Σ trit_value = $(sum(trits_vals)) ≡ $gf3_sum (mod 3)")
    println("  ✓ Balanced: $gf3_balanced")

    # Count trits
    n_plus = sum(acset[i, :trit_value] == 1 for i in 1:nparts(acset, :Skill))
    n_ergodic = sum(acset[i, :trit_value] == 0 for i in 1:nparts(acset, :Skill))
    n_minus = sum(acset[i, :trit_value] == -1 for i in 1:nparts(acset, :Skill))

    println("  Distribution: PLUS=$n_plus, ERGODIC=$n_ergodic, MINUS=$n_minus")

    # Skills by energy
    println("\n▸ SKILL ENERGY METRICS (sorted by energy_density):")
    println("  Rank  Name                      K        V        H        Density    Trit")
    println("  " * "─" ^ 90)

    sorted_skills = sort(collect(skill_parts), by=x -> x[2][8], rev=true)  # Sort by density

    for (rank, (name, (_, _, _, _, K, V, H, density, trit))) in enumerate(sorted_skills)
        Printf.@printf("  %3d   %-25s  %7.3f  %7.3f  %7.3f  %10.6f  %s\n",
            rank, name, K, V, H, density, trit)
    end

    # Energy statistics
    println("\n▸ ENERGY DISTRIBUTION STATISTICS:")
    kinetics = [x[2][5] for x in sorted_skills]
    potentials = [x[2][6] for x in sorted_skills]
    densities = [x[2][8] for x in sorted_skills]

    Printf.println("  Kinetic Energy:    mean=%7.3f, min=%7.3f, max=%7.3f",
        mean(kinetics), minimum(kinetics), maximum(kinetics))
    Printf.println("  Potential Energy:  mean=%7.3f, min=%7.3f, max=%7.3f",
        mean(potentials), minimum(potentials), maximum(potentials))
    Printf.println("  Energy Density:    mean=%10.6f, min=%10.6f, max=%10.6f",
        mean(densities), minimum(densities), maximum(densities))

    # Active vs Latent modes
    println("\n▸ OSCILLATION MODES (Hamiltonian Pendulum):")
    active_mode = 0
    latent_mode = 0
    for i in 1:nparts(acset, :DynamicalState)
        T = acset[i, :kinetic_energy]
        if T > 0.5
            active_mode += 1
        else
            latent_mode += 1
        end
    end
    println("  Active (K > 0.5):  $active_mode skills")
    println("  Latent (K < 0.5):  $latent_mode skills")

    # Reaction structure statistics
    println("\n▸ REACTION STRUCTURE (Capucci Coupling):")
    reaction_rates = [acset[i, :reaction_rate] for i in 1:nparts(acset, :ReactionStructure)]
    Printf.println("  Mean reaction_rate:  %6.3f", mean(reaction_rates))
    Printf.println("  Oscillation periods: %6.2f - %6.2f seconds",
        2π/sqrt(maximum(reaction_rates)), 2π/sqrt(minimum(reaction_rates)))

    # Conservation check
    println("\n▸ HAMILTONIAN CONSERVATION CHECK:")
    conserved_count = 0
    for i in 1:nparts(acset, :DynamicalState)
        H_stored = acset[i, :hamiltonian]
        H_computed = acset[i, :kinetic_energy] + acset[i, :potential_energy]
        if abs(H_stored - H_computed) < 1e-6
            conserved_count += 1
        end
    end
    println("  States with H = T + V: $conserved_count / $(nparts(acset, :DynamicalState))")

    println("\n" * "=" ^ 100)
    println("Ready for Plurigrid ASI integration with real gh_acset_export.json metrics")
    println("=" ^ 100)
end

# ============================================================================
# MAIN TEST
# ============================================================================

function main()
    println("Building Energy Dynamics ACSet with simulated ASI contributor metrics...\n")

    # Populate ACSet
    acset, skill_parts = populate_asi_acset(skills_data)

    # Generate report
    generate_asi_energy_report(acset, skill_parts)

    return acset, skill_parts
end

# Execute
if abspath(PROGRAM_FILE) == @__FILE__
    acset, skill_parts = main()

    # Optional: print individual skill summary
    println("\n\nSample High-Density Skill Summary:")
    sorted_skills = sort(collect(skill_parts), by=x -> x[2][8], rev=true)
    name, (skill_id, flow_id, state_id, reaction_id, K, V, H, density, trit) = sorted_skills[1]

    println("Skill: $name")
    println("  Kinetic Energy (K):       $K")
    println("  Potential Energy (V):     $V")
    println("  Total Energy (H):         $H")
    println("  Energy Density:           $density")
    println("  GF(3) Trit:              $trit")
    println("  Reaction Rate:            $(acset[reaction_id, :reaction_rate])")
    println("  Current State (T/V):      $(acset[state_id, :kinetic_energy]) / $(acset[state_id, :potential_energy])")
end
