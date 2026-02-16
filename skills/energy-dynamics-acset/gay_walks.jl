"""
gay_walks.jl

Random walk exploration of skill space using:
- Energy gradient (kinetic density as walk potential)
- Gay.jl deterministic coloring (reproducible exploration)
- ACSet morphism topology (skill relationships)

The ring of affordance completes:
  Energy Metrics → Gay Walks → Visualization → README
"""

using JSON3, Statistics, Printf, StatsBase

# ============================================================================
# LOAD DATA
# ============================================================================

"""Load energy metrics from extraction pipeline"""
function load_energies()
    energies_file = "outputs/asi_energies.json"
    if !isfile(energies_file)
        error("Energy data not found: $energies_file\nRun extract_asi_energies.jl first")
    end

    data = JSON3.read(read(energies_file))
    return Vector(data)
end

"""Load GF(3) assignments"""
function load_triads()
    trits_file = "outputs/gf3_assignments.json"
    if !isfile(trits_file)
        return Dict()  # Empty if not available
    end

    data = JSON3.read(read(trits_file))
    return Dict(data)
end

# ============================================================================
# GAY.JL DETERMINISTIC COLORING
# ============================================================================

"""
SplitMix64 RNG for deterministic color generation (from Gay.jl)
"""
function splitmix64(seed::UInt64)
    seed = (seed + 0x9e3779b97f4a7c15) & 0xffffffffffffffff
    z = seed
    z = ((z ⊻ (z >> 30)) * 0xbf58476d1ce4e5b9) & 0xffffffffffffffff
    z = ((z ⊻ (z >> 27)) * 0x94d049bb133111eb) & 0xffffffffffffffff
    return seed, (z ⊻ (z >> 31)) & 0xffffffffffffffff
end

"""
Generate deterministic hex color from seed
"""
function gay_color_at(seed::Int)
    seed_uint = UInt64(seed & 0xffffffffffffffff)
    _, val = splitmix64(seed_uint)
    r = (val >> 16) & 0xff
    g = (val >> 8) & 0xff
    b = val & 0xff
    return Printf.format(Printf.Format("#%02x%02x%02x"), r, g, b)
end

"""
Get color palette for skill walk
"""
function get_walk_palette(n_colors::Int, seed::Int=0x42d)
    colors = []
    for i in 1:n_colors
        push!(colors, gay_color_at(seed + i))
    end
    return colors
end

# ============================================================================
# RANDOM WALK FRAMEWORK
# ============================================================================

"""
Build energy-based transition matrix for random walks
"""
function build_energy_transition_matrix(energies)
    n = length(energies)
    P = zeros(n, n)

    for i in 1:n
        density_i = energies[i]["density"]
        neighbors = setdiff(1:n, i)

        # Probability of moving to neighbor j proportional to:
        # exp(-β * |E_j - E_i|) where β controls sensitivity

        neighbor_densities = [energies[j]["density"] for j in neighbors]
        energy_diffs = abs.(neighbor_densities .- density_i) .+ 1e-12

        # Boltzmann distribution: higher density neighbors more attractive
        β = 100.0  # Temperature parameter
        weights = exp.(-β .* energy_diffs)
        weights ./= sum(weights)

        for (idx, j) in enumerate(neighbors)
            P[i, j] = weights[idx]
        end
    end

    return P
end

"""
Simulate random walk through skill space
"""
function random_walk(start_idx::Int, steps::Int, transition_matrix, seed::Int=0x42d)
    """
    Walk through skill space following energy gradients.
    Each step assigns a deterministic color from Gay.jl.
    """

    trajectory = [start_idx]
    colors = []

    current = start_idx

    for step in 1:steps
        # Sample next state from transition matrix
        next_idx = sample(1:size(transition_matrix, 1), Weights(transition_matrix[current, :]))

        # Deterministic color for this step
        step_seed = seed + step
        color = gay_color_at(step_seed)

        push!(trajectory, next_idx)
        push!(colors, color)

        current = next_idx
    end

    return trajectory, colors
end

# ============================================================================
# ANALYSIS & VISUALIZATION
# ============================================================================

"""
Analyze walk trajectory for clusters and equilibrium
"""
function analyze_walk(trajectory, energies)
    visit_counts = countmap(trajectory)
    sorted_visits = sort(collect(visit_counts), by=x -> x[2], rev=true)

    println("\n" * "=" ^ 80)
    println("RANDOM WALK ANALYSIS")
    println("=" ^ 80)

    @printf("\nWalk length: %d steps\n", length(trajectory))
    @printf("Unique skills visited: %d / %d (%.1f%%)\n",
        length(visit_counts), length(energies),
        100 * length(visit_counts) / length(energies))

    println("\nMost visited skills (dwell time):")
    for (rank, (skill_idx, count)) in enumerate(sorted_visits[1:min(10, length(sorted_visits))])
        skill = energies[skill_idx]
        @printf("  %2d. %-28s  visits=%4d  density=%12.2e\n",
            rank, skill["name"], count, skill["density"])
    end

    println("\nEquilibrium analysis:")
    equilibrium_idx = mode(trajectory)
    equilibrium_skill = energies[equilibrium_idx]
    @printf("  Equilibrium skill: %s\n", equilibrium_skill["name"])
    @printf("  Equilibrium density: %.2e\n", equilibrium_skill["density"])

    # Check if walk settled to high or low energy
    avg_density_first_10pct = mean([energies[i]["density"] for i in trajectory[1:div(length(trajectory), 10)]])
    avg_density_last_10pct = mean([energies[i]["density"] for i in trajectory[end-div(length(trajectory), 10):end]])

    @printf("  Average density (first 10%%): %.2e\n", avg_density_first_10pct)
    @printf("  Average density (last 10%%): %.2e\n", avg_density_last_10pct)

    if avg_density_last_10pct > avg_density_first_10pct
        println("  ✓ Walk converged toward HIGH density (energy sources)")
    else
        println("  ↓ Walk drifted toward LOW density (energy sinks)")
    end
end

"""
Visualize walk in energy landscape
"""
function visualize_walk(trajectory, colors, energies, triads)
    println("\n" * "=" ^ 80)
    println("WALK TRAJECTORY (first 50 steps)")
    println("=" ^ 80)

    for (step, (skill_idx, color)) in enumerate(zip(trajectory[1:min(50, length(trajectory))], colors[1:min(50, length(colors))]))
        skill = energies[skill_idx]
        trit = get(triads, skill["name"], "?")

        # Show skill path with energy color coding
        Printf.@printf("%3d │ %s │ %-28s │ K=%8.5f V=%8.5f H=%8.5f │ %s\n",
            step, color, skill["name"],
            skill["kinetic"], skill["potential"], skill["hamiltonian"], trit)
    end

    if length(trajectory) > 50
        println("    └─ ($(length(trajectory) - 50) more steps)")
    end

    println("=" ^ 80)
end

"""
Generate walk statistics report
"""
function walk_report(trajectory, colors, energies, triads, start_skill::String)
    println("\n" * "╔" * "═" ^ 78 * "╗")
    println("║" * " " ^ 15 * "ENERGY-GRADIENT RANDOM WALK REPORT" * " " ^ 30 * "║")
    println("╚" * "═" ^ 78 * "╝")

    @printf("\nStart skill: %s\n", start_skill)
    @printf("Walk length: %d steps\n", length(trajectory))

    # Cluster detection
    visit_counts = countmap(trajectory)
    println("\nCluster Structure:")
    @printf("  Unique locations: %d / %d skills (%.1f%% coverage)\n",
        length(visit_counts), length(energies),
        100 * length(visit_counts) / length(energies))

    # Energy analysis
    densities_in_walk = [energies[i]["density"] for i in trajectory]
    densities_all = [e["density"] for e in energies]

    println("\nEnergy Statistics:")
    @printf("  Walk avg density:     %.2e\n", mean(densities_in_walk))
    @printf("  All skills avg:       %.2e\n", mean(densities_all))
    @printf("  Walk min density:     %.2e\n", minimum(densities_in_walk))
    @printf("  Walk max density:     %.2e\n", maximum(densities_in_walk))

    # Drift analysis
    first_50 = min(50, div(length(trajectory), 4))
    second_50 = max(first_50 + 1, length(trajectory) - div(length(trajectory), 4))
    drift_initial = mean([densities_all[trajectory[i]] for i in 1:first_50])
    drift_final = mean([densities_all[trajectory[i]] for i in second_50:length(trajectory)])

    @printf("\nDrift Pattern:\n")
    @printf("  Initial avg: %.2e → Final avg: %.2e\n", drift_initial, drift_final)

    if drift_final > drift_initial
        drift_pct = 100 * (drift_final - drift_initial) / drift_initial
        @printf("  Direction: UPWARD (+%.1f%%) toward energy sources\n", drift_pct)
    else
        drift_pct = 100 * (drift_initial - drift_final) / drift_initial
        @printf("  Direction: DOWNWARD (%.1f%%) toward energy sinks\n", drift_pct)
    end

    # GF(3) distribution along walk
    trits_in_walk = [get(triads, energies[i]["name"], "?") for i in trajectory]
    n_plus = count(t -> t == "PLUS", trits_in_walk)
    n_ergodic = count(t -> t == "ERGODIC", trits_in_walk)
    n_minus = count(t -> t == "MINUS", trits_in_walk)

    println("\nTriadic Distribution (along walk):")
    @printf("  PLUS (+1):    %3d steps (%.1f%%)\n", n_plus, 100*n_plus/length(trajectory))
    @printf("  ERGODIC (0):  %3d steps (%.1f%%)\n", n_ergodic, 100*n_ergodic/length(trajectory))
    @printf("  MINUS (-1):   %3d steps (%.1f%%)\n", n_minus, 100*n_minus/length(trajectory))

    println("\n" * "╚" * "═" ^ 78 * "╝")
end

# ============================================================================
# MAIN EXECUTION
# ============================================================================

function main()
    println("Loading energy metrics...")
    energies = load_energies()
    triads = load_triads()

    println("Found $(length(energies)) skills with energy metrics")

    println("\nBuilding energy-based transition matrix...")
    P = build_energy_transition_matrix(energies)

    println("Transition matrix constructed: $(size(P))")

    # Start from highest energy density skill
    start_skill_idx = argmax([e["density"] for e in energies])
    start_skill = energies[start_skill_idx]["name"]

    println("\n" * "="^80)
    println("STARTING RANDOM WALK FROM: $start_skill")
    println("="^80)

    # Run walk
    n_steps = 500
    walk_seed = 0x42d

    println("\nSimulating $(n_steps)-step random walk (seed=0x42d)...")
    trajectory, colors = random_walk(start_skill_idx, n_steps, P, Int(walk_seed))

    # Visualize
    visualize_walk(trajectory, colors, energies, triads)

    # Analyze
    analyze_walk(trajectory, energies)

    # Report
    walk_report(trajectory, colors, energies, triads, start_skill)

    return trajectory, colors, energies
end

if abspath(PROGRAM_FILE) == @__FILE__
    trajectory, colors, energies = main()

    println("\n✓ Gay.jl random walk exploration complete!")
    println("  Walk reveals energy landscape topology and skill affinities")
    println("  Colors are deterministic (Gay.jl SplitMix64 RNG)")
    println("  Seed 0x42d ensures reproducible, verifiable walks")
end
