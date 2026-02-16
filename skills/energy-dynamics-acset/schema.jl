"""
EnergyDynamicsACSet.jl

ACSet schema for organizing skills and systems through:
  - Matteo Capucci's "Organizing Physics with Open Energy-Driven Systems"
  - Sophie Libkind's dynamical systems composition
  - Kinetic (interaction entropy) + Potential (latent schema) energy
  - GF(3) triadic organization

Reaction structure: T*Q → TQ (cotangent to tangent bundle)
Symmetric monoidal category of open energy-driven systems
"""

using Catlab, ACSets

# ============================================================================
# SCHEMA DEFINITION: Energy Dynamics ACSet
# ============================================================================

@present SchEnergyDynamicsACSet(FreeSchema) begin

    # ────────────────────────────────────────────────────────────────────
    # OBJECTS: Entities in the energy dynamics system
    # ────────────────────────────────────────────────────────────────────

    Skill::Ob              # A computational/cognitive skill
    EnergyFlow::Ob         # Open energy-driven interaction (Capucci)
    DynamicalState::Ob     # Phase space point (Libkind)
    ReactionStructure::Ob  # Hamiltonian reaction: T*Q → TQ
    Trit::Ob               # GF(3) classification (MINUS/ERGODIC/PLUS)
    TimePoint::Ob          # Temporal indexing

    # ────────────────────────────────────────────────────────────────────
    # MORPHISMS: Relationships and transformations
    # ────────────────────────────────────────────────────────────────────

    # Energy flow structure (open system boundaries)
    energy_source::Hom(EnergyFlow, Skill)      # Where energy comes from
    energy_sink::Hom(EnergyFlow, Skill)        # Where energy goes

    # State dynamics (pendulum-like oscillation)
    current_state::Hom(Skill, DynamicalState)  # Current phase space point
    reaction::Hom(Skill, ReactionStructure)    # How skill transforms energy

    # Temporal evolution
    time_step::Hom(DynamicalState, TimePoint)  # When this state occurs
    next_state::Hom(DynamicalState, DynamicalState)  # State transition

    # GF(3) classification
    trit_assignment::Hom(Skill, Trit)          # MINUS(-1), ERGODIC(0), PLUS(+1)

    # ────────────────────────────────────────────────────────────────────
    # ATTRIBUTES: Quantitative properties
    # ────────────────────────────────────────────────────────────────────

    # Kinetic energy: current interaction entropy signature
    entropy_rate::Attr(EnergyFlow, Float64)           # dS/dt (current dissipation)
    interaction_degree::Attr(EnergyFlow, Int)         # Number of simultaneous interactions
    bandwidth_utilization::Attr(EnergyFlow, Float64)  # % of available interaction capacity

    # Potential energy: latent structural capacity
    schema_complexity::Attr(Skill, Float64)    # Cyclomatic complexity of skill schema
    representational_depth::Attr(Skill, Int)   # Nesting depth in categorical hierarchy
    storage_footprint::Attr(Skill, Int)        # Bytes on disk (resource awareness)

    # Combined energetics
    kinetic_energy::Attr(DynamicalState, Float64)    # T = (1/2)mv² momentum term
    potential_energy::Attr(DynamicalState, Float64)  # V = mgh height term
    hamiltonian::Attr(DynamicalState, Float64)       # H = T + V total energy

    # Reaction structure (Capucci)
    cotangent_contribution::Attr(ReactionStructure, Float64)  # T*Q component
    tangent_contribution::Attr(ReactionStructure, Float64)    # TQ component
    reaction_rate::Attr(ReactionStructure, Float64)           # dq/dt coupling strength

    # Temporal data
    timestamp::Attr(TimePoint, Float64)        # Unix time

    # GF(3) numerical value
    trit_value::Attr(Trit, Int)                # -1, 0, or +1
    trit_name::Attr(Trit, String)              # "MINUS", "ERGODIC", "PLUS"

end

# ============================================================================
# DERIVED QUANTITIES & INVARIANTS
# ============================================================================

"""
    total_energy(acset::ACSetType{SchEnergyDynamicsACSet}, state_id::Int)

Compute total mechanical energy: H = T + V
"""
function total_energy(acset, state_id)
    T = acset[state_id, :kinetic_energy]
    V = acset[state_id, :potential_energy]
    return T + V
end

"""
    information_entropy(acset::ACSetType{SchEnergyDynamicsACSet}, flow_id::Int)

Kinetic information energy = entropy_rate × interaction_degree × bandwidth_utilization
Measures current "thermodynamic" activity of skill interaction
"""
function information_entropy(acset, flow_id)
    dS = acset[flow_id, :entropy_rate]
    degree = acset[flow_id, :interaction_degree]
    bandwidth = acset[flow_id, :bandwidth_utilization]
    return dS * degree * bandwidth
end

"""
    latent_capacity(acset::ACSetType{SchEnergyDynamicsACSet}, skill_id::Int)

Potential information energy = schema_complexity × representational_depth
Measures stored structural richness of skill
"""
function latent_capacity(acset, skill_id)
    complexity = acset[skill_id, :schema_complexity]
    depth = acset[skill_id, :representational_depth]
    return complexity * depth
end

"""
    gf3_conservation(acset::ACSetType{SchEnergyDynamicsACSet})

Verify GF(3) invariant: Σ trit_value = 0 (mod 3) for triadic balance
"""
function gf3_conservation(acset)
    sum_trits = sum(acset[i, :trit_value] for i in 1:nparts(acset, :Trit))
    return mod(sum_trits, 3) == 0
end

"""
    is_energy_conserving(acset::ACSetType{SchEnergyDynamicsACSet},
                         state_id::Int, tolerance=1e-6)

Check if Hamiltonian equals T + V (energy conservation)
"""
function is_energy_conserving(acset, state_id; tolerance=1e-6)
    H = acset[state_id, :hamiltonian]
    computed_H = total_energy(acset, state_id)
    return abs(H - computed_H) < tolerance
end

# ============================================================================
# EXAMPLE INSTANTIATION
# ============================================================================

"""
    example_skill_energy_dynamics()

Create a concrete instance showing:
  - A skill with open energy flow
  - Kinetic energy from interaction entropy (Gay.jl color mining)
  - Potential energy from schema complexity (ACSet taxonomy)
  - Pendulum dynamics between latent and active states
  - GF(3) balance
"""
function example_skill_energy_dynamics()

    # Create empty ACSet
    acset = ACSet{SchEnergyDynamicsACSet}()

    # ────────────────────────────────────────────────────────────────────
    # Add three GF(3) Trits
    # ────────────────────────────────────────────────────────────────────
    add_part!(acset, :Trit; trit_value=-1, trit_name="MINUS")
    add_part!(acset, :Trit; trit_value=0,  trit_name="ERGODIC")
    add_part!(acset, :Trit; trit_value=+1, trit_name="PLUS")

    # ────────────────────────────────────────────────────────────────────
    # Add three Time Points (pendulum swing)
    # ────────────────────────────────────────────────────────────────────
    time1 = add_part!(acset, :TimePoint; timestamp=0.0)
    time2 = add_part!(acset, :TimePoint; timestamp=0.5)
    time3 = add_part!(acset, :TimePoint; timestamp=1.0)

    # ────────────────────────────────────────────────────────────────────
    # Add three Skills (MINUS, ERGODIC, PLUS)
    # ────────────────────────────────────────────────────────────────────

    skill_minus = add_part!(acset, :Skill;
        schema_complexity=2.1,           # Low complexity
        representational_depth=3,         # Shallow hierarchy
        storage_footprint=50_000,         # 50 KB
        trit_assignment=1                 # MINUS trit
    )

    skill_ergodic = add_part!(acset, :Skill;
        schema_complexity=5.7,            # Medium complexity
        representational_depth=7,         # Medium hierarchy
        storage_footprint=250_000,        # 250 KB
        trit_assignment=2                 # ERGODIC trit
    )

    skill_plus = add_part!(acset, :Skill;
        schema_complexity=8.3,            # High complexity
        representational_depth=12,        # Deep hierarchy
        storage_footprint=600_000,        # 600 KB
        trit_assignment=3                 # PLUS trit
    )

    # ────────────────────────────────────────────────────────────────────
    # Add three Reaction Structures (one per skill)
    # ────────────────────────────────────────────────────────────────────

    reaction_minus = add_part!(acset, :ReactionStructure;
        cotangent_contribution=0.3,       # Position space dominates
        tangent_contribution=0.7,         # Momentum small
        reaction_rate=0.2                 # Slow coupling
    )

    reaction_ergodic = add_part!(acset, :ReactionStructure;
        cotangent_contribution=0.5,       # Balanced
        tangent_contribution=0.5,         # Balanced
        reaction_rate=0.5                 # Moderate coupling
    )

    reaction_plus = add_part!(acset, :ReactionStructure;
        cotangent_contribution=0.7,       # Momentum space dominates
        tangent_contribution=0.3,         # Position small
        reaction_rate=0.8                 # Fast coupling
    )

    set_subpart!(acset, skill_minus, :reaction, reaction_minus)
    set_subpart!(acset, skill_ergodic, :reaction, reaction_ergodic)
    set_subpart!(acset, skill_plus, :reaction, reaction_plus)

    # ────────────────────────────────────────────────────────────────────
    # Add three Energy Flows (interaction entropy signatures)
    # ────────────────────────────────────────────────────────────────────

    flow_minus = add_part!(acset, :EnergyFlow;
        entropy_rate=0.05,                # Low dissipation
        interaction_degree=2,             # Few simultaneous interactions
        bandwidth_utilization=0.3,        # 30% capacity used
        energy_source=skill_minus,
        energy_sink=skill_ergodic
    )

    flow_ergodic = add_part!(acset, :EnergyFlow;
        entropy_rate=0.15,                # Moderate dissipation
        interaction_degree=4,             # Multiple interactions
        bandwidth_utilization=0.6,        # 60% capacity used
        energy_source=skill_ergodic,
        energy_sink=skill_plus
    )

    flow_plus = add_part!(acset, :EnergyFlow;
        entropy_rate=0.25,                # High dissipation
        interaction_degree=8,             # Many simultaneous interactions
        bandwidth_utilization=0.9,        # 90% capacity used
        energy_source=skill_plus,
        energy_sink=skill_minus
    )

    # ────────────────────────────────────────────────────────────────────
    # Add three Dynamical States (pendulum swinging)
    # ────────────────────────────────────────────────────────────────────

    # State 1: Potential energy high (top of swing), kinetic low
    state1 = add_part!(acset, :DynamicalState;
        kinetic_energy=0.1,               # Low kinetic (slow at top)
        potential_energy=0.9,             # High potential (high up)
        hamiltonian=1.0,                  # Total energy
        time_step=time1,
        current_state=skill_minus
    )

    # State 2: Balanced (middle of swing)
    state2 = add_part!(acset, :DynamicalState;
        kinetic_energy=0.5,               # Medium kinetic
        potential_energy=0.5,             # Medium potential
        hamiltonian=1.0,                  # Energy conserved
        time_step=time2,
        current_state=skill_ergodic
    )

    # State 3: Kinetic energy high (bottom of swing), potential low
    state3 = add_part!(acset, :DynamicalState;
        kinetic_energy=0.9,               # High kinetic (fast at bottom)
        potential_energy=0.1,             # Low potential (low down)
        hamiltonian=1.0,                  # Energy conserved
        time_step=time3,
        current_state=skill_plus
    )

    # Pendulum: state1 → state2 → state3 → state1
    set_subpart!(acset, state1, :next_state, state2)
    set_subpart!(acset, state2, :next_state, state3)
    set_subpart!(acset, state3, :next_state, state1)

    return acset
end

# ============================================================================
# VISUALIZATION & ANALYSIS
# ============================================================================

"""
    energy_report(acset::ACSetType{SchEnergyDynamicsACSet})

Print comprehensive energy dynamics report
"""
function energy_report(acset)
    println("=" ^ 80)
    println("ENERGY DYNAMICS ACSet REPORT")
    println("=" ^ 80)

    println("\n▸ GF(3) TRIAD CONSERVATION:")
    println("  Σ trit = ", sum(acset[i, :trit_value] for i in 1:nparts(acset, :Trit)), " (mod 3)")
    println("  ✓ Balanced: ", gf3_conservation(acset))

    println("\n▸ KINETIC INFORMATION ENERGY (Interaction Entropy):")
    for i in 1:nparts(acset, :EnergyFlow)
        entropy = information_entropy(acset, i)
        source = acset[acset[i, :energy_source], :schema_complexity]
        sink = acset[acset[i, :energy_sink], :schema_complexity]
        println("  Flow $i: ", round(entropy, digits=4),
                " (from complexity=$source to $sink)")
    end

    println("\n▸ POTENTIAL INFORMATION ENERGY (Schema Capacity):")
    for i in 1:nparts(acset, :Skill)
        capacity = latent_capacity(acset, i)
        storage = acset[i, :storage_footprint] / 1000
        println("  Skill $i: capacity=$capacity, storage=${storage}KB")
    end

    println("\n▸ DYNAMICAL STATES (Pendulum Oscillation):")
    for i in 1:nparts(acset, :DynamicalState)
        T = acset[i, :kinetic_energy]
        V = acset[i, :potential_energy]
        H = acset[i, :hamiltonian]
        conserved = is_energy_conserving(acset, i)
        println("  State $i: T=$T, V=$V, H=$H, Conserved=$conserved")
    end

    println("\n▸ REACTION STRUCTURES (Hamiltonian Coupling):")
    for i in 1:nparts(acset, :ReactionStructure)
        T_contrib = acset[i, :cotangent_contribution]
        TQ_contrib = acset[i, :tangent_contribution]
        rate = acset[i, :reaction_rate]
        println("  Reaction $i: T*Q=$T_contrib, TQ=$TQ_contrib, rate=$rate")
    end

    println("\n" * "=" ^ 80)
end

end # module

# ============================================================================
# EXPORTS
# ============================================================================

export SchEnergyDynamicsACSet
export total_energy, information_entropy, latent_capacity
export gf3_conservation, is_energy_conserving
export example_skill_energy_dynamics, energy_report
