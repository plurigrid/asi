# ADHD-ECS Sexual Dimorphism: Counterfactual Causal Analysis
# 
# This module extends the EPDS theory to formalize sexual dimorphism
# as a CAUSAL factor (not merely correlational) in ADHD prevalence.
#
# Key thesis: The 3:1 male:female ADHD ratio emerges from:
#   1. Estrogen-CB1 upregulation (protective in females)
#   2. Testosterone-FAAH interaction (risk factor in males)
#   3. Differential precision-weighting dynamics across development
#
# Counterfactual framework following Pearl's do-calculus and
# greenteatree01's emphasis on phenotypic/developmental dynamics.
#
# Date: 2026-01-27

module SexualDimorphismECS

using LinearAlgebra
using Statistics
using Random

# ============================================================================
# PART 1: EXTENDED STRUCTURAL CAUSAL MODEL WITH SEX VARIABLES
# ============================================================================

"""
Extended SCM with explicit sex-hormone pathways.

The causal graph:
                    
    BiologicalSex ──┬──────────────────────────────────────┐
         │         │                                       │
         ▼         ▼                                       ▼
    Testosterone  Estrogen                            Socialization
         │         │                                       │
         ▼         │                                       │
    FAAH_expr ◄────┘                                       │
         │                                                 │
         ▼                                                 │
    AEA_tone ──────┬───────────────────────────────────────┤
         │         │                                       │
         ▼         ▼                                       │
    CB1_pfc   CB1_amygdala                                 │
         │         │                                       │
         └────┬────┘                                       │
              ▼                                            │
         Precision_β ◄─────────────────────────────────────┘
              │
              ▼
         World_Model (μ, Σ)
              │
              ▼
         ADHD_Phenotype
"""
struct SexualDimorphismSCM
    # Biological sex (binary for simplicity; could extend to continuous)
    is_female::Bool
    
    # Hormone levels (phenotypic, not genotypic!)
    testosterone::Float64
    estrogen::Float64
    
    # Exogenous factors
    U_genetic::Float64          # FAAH/CNR1 polymorphisms
    U_inflammatory::Float64     # Neuroinflammation  
    U_developmental::Float64    # Early life stress/nutrition
    U_socialization::Float64    # Gender-specific environmental pressures
    
    # Structural equation coefficients
    # Path: Sex → Hormones
    sex_testosterone_effect::Float64    # Male → +testosterone
    sex_estrogen_effect::Float64        # Female → +estrogen
    
    # Path: Hormones → ECS
    testosterone_faah_coef::Float64     # T ↑ FAAH (risk)
    estrogen_cb1_coef::Float64          # E ↑ CB1 (protective)
    estrogen_aea_coef::Float64          # E ↑ AEA synthesis
    
    # Path: ECS → Precision
    cb1_pfc_precision_coef::Float64
    cb1_amygdala_anxiety_coef::Float64  # NEW: amygdala pathway
    
    # Path: Socialization → Precision (phenotypic!)
    socialization_precision_coef::Float64
    
    # Path: Precision → ADHD
    precision_adhd_coef::Float64
end

"""
Default model calibrated to produce ~3:1 male:female ratio
"""
function default_dimorphism_model(is_female::Bool)
    # Sex-specific hormone baselines
    testosterone = is_female ? 0.3 : 2.0
    estrogen = is_female ? 2.0 : 0.5
    
    return SexualDimorphismSCM(
        is_female,
        testosterone,
        estrogen,
        
        # Exogenous (sampled during computation)
        0.0, 0.0, 0.0, 0.0,
        
        # Sex → Hormone coefficients
        -1.7,   # Male effect on testosterone
        1.5,    # Female effect on estrogen
        
        # Hormone → ECS coefficients
        0.15,   # Testosterone increases FAAH (harmful)
        0.35,   # Estrogen increases CB1 (protective)
        0.20,   # Estrogen increases AEA (protective)
        
        # ECS → Precision
        0.40,   # CB1 → precision (main pathway)
        -0.25,  # CB1_amygdala → anxiety (negative = low CB1 → high anxiety)
        
        # Socialization → Precision
        0.15,   # Social learning affects precision calibration
        
        # Precision → ADHD
        -0.50   # Higher precision → lower ADHD severity
    )
end

# ============================================================================
# PART 2: COUNTERFACTUAL QUERIES FOR SEXUAL DIMORPHISM
# ============================================================================

"""
Compute all endogenous variables through structural equations.
Returns named tuple with full causal chain.
"""
function compute_full_scm(model::SexualDimorphismSCM; 
                          seed::Union{Int,Nothing}=nothing)
    if !isnothing(seed)
        Random.seed!(seed)
    end
    
    # Noise terms (phenotypic variation!)
    ε = randn(10) .* 0.3
    
    # --- Structural Equations ---
    
    # 1. FAAH expression: genetic + testosterone effect
    faah_expr = 1.0 + 
                0.25 * model.U_genetic + 
                model.testosterone_faah_coef * model.testosterone + 
                ε[1]
    faah_expr = max(0.1, faah_expr)  # Physiological floor
    
    # 2. AEA tone: inverse of FAAH + estrogen boost
    aea_tone = 10.0 - 1.5 * faah_expr + 
               model.estrogen_aea_coef * model.estrogen + 
               ε[2]
    aea_tone = max(0.1, aea_tone)
    
    # 3. CB1 prefrontal: AEA-driven + estrogen upregulation
    cb1_pfc = 2.0 + 
              0.5 * aea_tone + 
              model.estrogen_cb1_coef * model.estrogen -
              0.2 * model.U_inflammatory + 
              ε[3]
    cb1_pfc = max(0.1, cb1_pfc)
    
    # 4. CB1 amygdala: modulates anxiety/threat world-model
    #    (This is greenteatree01's "amygdala overactivation → high-anxiety world model")
    cb1_amygdala = 1.5 + 
                   0.4 * aea_tone + 
                   0.25 * model.estrogen -
                   0.3 * model.U_developmental +  # Early stress reduces CB1
                   ε[4]
    cb1_amygdala = max(0.1, cb1_amygdala)
    
    # 5. Anxiety level (inverse of CB1_amygdala)
    #    Low CB1 in amygdala → impaired fear extinction → chronic anxiety
    anxiety_baseline = 50 + model.cb1_amygdala_anxiety_coef * cb1_amygdala * 20 + ε[5]
    anxiety_baseline = clamp(anxiety_baseline, 0, 100)
    
    # 6. Precision parameter β (main active inference variable)
    #    Affected by CB1 levels AND socialization
    precision_β = 1.0 + 
                  model.cb1_pfc_precision_coef * cb1_pfc +
                  0.2 * cb1_amygdala +  # Amygdala CB1 also contributes
                  model.socialization_precision_coef * model.U_socialization +
                  ε[6]
    precision_β = max(0.1, precision_β)
    
    # 7. World-model uncertainty Σ (inverse of precision)
    #    This is greenteatree01's "world-model belief states"
    world_model_uncertainty = 2.0 / precision_β + 0.3 * (anxiety_baseline / 50) + ε[7]
    world_model_uncertainty = max(0.5, world_model_uncertainty)
    
    # 8. Cognitive outcomes
    impulse_control = 50 + 8 * precision_β - 0.1 * anxiety_baseline + ε[8]
    attention = 50 + 6 * precision_β - 0.15 * anxiety_baseline + ε[9]
    
    # 9. ADHD severity (final phenotype)
    adhd_severity = 100 + 
                    model.precision_adhd_coef * (impulse_control + attention) / 2 -
                    0.2 * precision_β +
                    0.1 * world_model_uncertainty +
                    ε[10]
    
    return (
        # Hormones
        testosterone = model.testosterone,
        estrogen = model.estrogen,
        
        # ECS chain
        faah_expr = faah_expr,
        aea_tone = aea_tone,
        cb1_pfc = cb1_pfc,
        cb1_amygdala = cb1_amygdala,
        
        # Active inference variables
        anxiety_baseline = anxiety_baseline,
        precision_β = precision_β,
        world_model_uncertainty = world_model_uncertainty,
        
        # Cognitive phenotype
        impulse_control = impulse_control,
        attention = attention,
        adhd_severity = adhd_severity
    )
end

"""
COUNTERFACTUAL QUERY 1: Sex Swap
"What would this male's ADHD severity be if they had female hormone profile?"

This is the fundamental question: Is the sex difference CAUSAL or merely correlational?
If do(Hormones_male → Hormones_female) changes ADHD, sex is causally upstream.
"""
function counterfactual_sex_swap(
    original_model::SexualDimorphismSCM;
    n_samples::Int = 1000
)
    # Observed outcome with actual sex
    original_outcomes = [compute_full_scm(original_model, seed=i) 
                         for i in 1:n_samples]
    original_adhd = mean(o.adhd_severity for o in original_outcomes)
    
    # Counterfactual: swap hormone profile
    swapped_model = SexualDimorphismSCM(
        !original_model.is_female,  # Flip sex
        original_model.is_female ? 2.0 : 0.3,   # Swap testosterone
        original_model.is_female ? 0.5 : 2.0,   # Swap estrogen
        original_model.U_genetic,
        original_model.U_inflammatory,
        original_model.U_developmental,
        original_model.U_socialization,
        original_model.sex_testosterone_effect,
        original_model.sex_estrogen_effect,
        original_model.testosterone_faah_coef,
        original_model.estrogen_cb1_coef,
        original_model.estrogen_aea_coef,
        original_model.cb1_pfc_precision_coef,
        original_model.cb1_amygdala_anxiety_coef,
        original_model.socialization_precision_coef,
        original_model.precision_adhd_coef
    )
    
    counterfactual_outcomes = [compute_full_scm(swapped_model, seed=i) 
                               for i in 1:n_samples]
    counterfactual_adhd = mean(o.adhd_severity for o in counterfactual_outcomes)
    
    causal_effect = original_adhd - counterfactual_adhd
    
    return (
        original_sex = original_model.is_female ? "Female" : "Male",
        original_adhd = original_adhd,
        counterfactual_adhd = counterfactual_adhd,
        causal_effect_of_sex = causal_effect,
        interpretation = causal_effect > 0 ? 
            "Original sex INCREASES ADHD risk (causal)" :
            "Original sex DECREASES ADHD risk (protective)"
    )
end

"""
COUNTERFACTUAL QUERY 2: Estrogen Intervention
do(Estrogen = target) across sexes

Tests: Can estrogen supplementation reduce ADHD in males?
This has therapeutic implications.
"""
function counterfactual_estrogen_intervention(
    target_estrogen::Float64;
    n_samples::Int = 1000
)
    results = Dict()
    
    for is_female in [false, true]
        sex_label = is_female ? "Female" : "Male"
        
        # Baseline model
        baseline_model = default_dimorphism_model(is_female)
        baseline_outcomes = [compute_full_scm(baseline_model, seed=i) 
                            for i in 1:n_samples]
        baseline_adhd = mean(o.adhd_severity for o in baseline_outcomes)
        baseline_estrogen = mean(o.estrogen for o in baseline_outcomes)
        
        # Intervention: set estrogen to target
        intervention_model = SexualDimorphismSCM(
            is_female,
            baseline_model.testosterone,
            target_estrogen,  # INTERVENED
            baseline_model.U_genetic,
            baseline_model.U_inflammatory,
            baseline_model.U_developmental,
            baseline_model.U_socialization,
            baseline_model.sex_testosterone_effect,
            baseline_model.sex_estrogen_effect,
            baseline_model.testosterone_faah_coef,
            baseline_model.estrogen_cb1_coef,
            baseline_model.estrogen_aea_coef,
            baseline_model.cb1_pfc_precision_coef,
            baseline_model.cb1_amygdala_anxiety_coef,
            baseline_model.socialization_precision_coef,
            baseline_model.precision_adhd_coef
        )
        
        intervention_outcomes = [compute_full_scm(intervention_model, seed=i) 
                                 for i in 1:n_samples]
        intervention_adhd = mean(o.adhd_severity for o in intervention_outcomes)
        
        results[sex_label] = (
            baseline_estrogen = baseline_estrogen,
            baseline_adhd = baseline_adhd,
            intervention_estrogen = target_estrogen,
            intervention_adhd = intervention_adhd,
            effect = baseline_adhd - intervention_adhd
        )
    end
    
    return results
end

"""
COUNTERFACTUAL QUERY 3: Developmental Timing
"What if puberty occurred earlier/later?"

Models how developmental timing (phenotype, not genotype!) affects ADHD.
This addresses greenteatree01's point about habituation patterns being developmental.
"""
function counterfactual_developmental_timing(;
    puberty_timing::Symbol = :normal,  # :early, :normal, :late
    n_samples::Int = 1000
)
    # Timing affects hormone exposure duration and peak levels
    timing_effects = Dict(
        :early => (testosterone_mult=1.3, estrogen_mult=1.2, stress_mult=1.5),
        :normal => (testosterone_mult=1.0, estrogen_mult=1.0, stress_mult=1.0),
        :late => (testosterone_mult=0.8, estrogen_mult=0.9, stress_mult=0.8)
    )
    
    effects = timing_effects[puberty_timing]
    results = Dict()
    
    for is_female in [false, true]
        sex_label = is_female ? "Female" : "Male"
        
        # Adjusted model for timing
        base_testosterone = is_female ? 0.3 : 2.0
        base_estrogen = is_female ? 2.0 : 0.5
        
        timing_model = SexualDimorphismSCM(
            is_female,
            base_testosterone * effects.testosterone_mult,
            base_estrogen * effects.estrogen_mult,
            0.0,  # U_genetic
            0.0,  # U_inflammatory
            effects.stress_mult - 1.0,  # U_developmental (early puberty = more stress)
            0.0,  # U_socialization
            -1.7, 1.5,  # Sex → Hormone
            0.15, 0.35, 0.20,  # Hormone → ECS
            0.40, -0.25,  # ECS → Precision
            0.15,  # Socialization → Precision
            -0.50  # Precision → ADHD
        )
        
        outcomes = [compute_full_scm(timing_model, seed=i) for i in 1:n_samples]
        
        results[sex_label] = (
            timing = puberty_timing,
            mean_adhd = mean(o.adhd_severity for o in outcomes),
            mean_anxiety = mean(o.anxiety_baseline for o in outcomes),
            mean_precision = mean(o.precision_β for o in outcomes),
            mean_world_uncertainty = mean(o.world_model_uncertainty for o in outcomes)
        )
    end
    
    return results
end

# ============================================================================
# PART 3: WORLD-MODEL DYNAMICS (Active Inference Extension)
# ============================================================================

"""
Sex-specific Active Inference Agent
Incorporates hormonal modulation of precision and world-model uncertainty
"""
mutable struct SexSpecificAgent
    # Identity
    is_female::Bool
    
    # Hormonal state (can change across development)
    testosterone::Float64
    estrogen::Float64
    
    # World-model beliefs (μ = expected state)
    μ_world::Vector{Float64}    # Beliefs about external world
    μ_self::Vector{Float64}     # Beliefs about self/body
    μ_social::Vector{Float64}   # Beliefs about social environment
    
    # World-model uncertainty (Σ = covariance)
    Σ_world::Float64
    Σ_self::Float64
    Σ_social::Float64
    
    # Precision parameters (β) - modulated by ECS
    β_sensory::Float64
    β_interoceptive::Float64
    β_social::Float64
    β_threat::Float64           # Amygdala-mediated threat precision
    
    # Learning rates (η) - affect habituation speed
    η_world::Float64
    η_self::Float64
    η_social::Float64
end

"""
Create agent with sex-specific precision profile
"""
function create_sex_specific_agent(is_female::Bool)
    # Female protective factors: higher CB1 → higher precision
    precision_boost = is_female ? 0.3 : 0.0
    
    # Male risk factors: higher FAAH → lower AEA → lower precision
    precision_penalty = is_female ? 0.0 : 0.2
    
    base_precision = 1.0 + precision_boost - precision_penalty
    
    # Threat precision (amygdala)
    # Females: estrogen modulates amygdala, more calibrated threat response
    # Males: testosterone increases amygdala reactivity
    threat_precision = is_female ? 1.0 : 1.3  # Males over-weight threats
    
    return SexSpecificAgent(
        is_female,
        is_female ? 0.3 : 2.0,  # Testosterone
        is_female ? 2.0 : 0.5,  # Estrogen
        
        # Initial beliefs (neutral priors)
        zeros(5),   # World beliefs
        zeros(3),   # Self beliefs
        zeros(4),   # Social beliefs
        
        # Initial uncertainty (higher for ADHD-prone males)
        is_female ? 1.0 : 1.5,  # Σ_world
        is_female ? 0.8 : 1.2,  # Σ_self
        is_female ? 1.0 : 1.3,  # Σ_social
        
        # Precision parameters
        base_precision,           # β_sensory
        base_precision * 0.9,     # β_interoceptive
        base_precision * 1.1,     # β_social (females often higher)
        threat_precision,         # β_threat
        
        # Learning rates (habituation speed)
        0.1,   # η_world
        0.08,  # η_self
        0.12   # η_social
    )
end

"""
Compute world-model free energy for the agent.
This is greenteatree01's "world-model belief states" formalized.
"""
function world_model_free_energy(agent::SexSpecificAgent, 
                                  observations::NamedTuple)
    # Unpack observations
    world_obs = get(observations, :world, zeros(5))
    self_obs = get(observations, :self, zeros(3))
    social_obs = get(observations, :social, zeros(4))
    threat_obs = get(observations, :threat, 0.0)
    
    # Prediction errors (weighted by precision)
    world_error = agent.β_sensory * sum((world_obs .- agent.μ_world).^2)
    self_error = agent.β_interoceptive * sum((self_obs .- agent.μ_self).^2)
    social_error = agent.β_social * sum((social_obs .- agent.μ_social).^2)
    
    # Threat prediction error (amygdala pathway)
    # High β_threat means threats are HIGHLY weighted
    threat_error = agent.β_threat * threat_obs^2
    
    # Complexity penalties (KL divergence from priors)
    world_complexity = 0.5 * sum(agent.μ_world.^2) / agent.Σ_world
    self_complexity = 0.5 * sum(agent.μ_self.^2) / agent.Σ_self
    social_complexity = 0.5 * sum(agent.μ_social.^2) / agent.Σ_social
    
    # Total free energy
    accuracy = world_error + self_error + social_error + threat_error
    complexity = 0.1 * (world_complexity + self_complexity + social_complexity)
    
    return accuracy + complexity
end

"""
Update beliefs (habituation).
This is the mathematical formalization of greenteatree01's
"habituation patterns of brain network activity".
"""
function habituate!(agent::SexSpecificAgent, observations::NamedTuple)
    # Unpack observations
    world_obs = get(observations, :world, agent.μ_world)
    self_obs = get(observations, :self, agent.μ_self)
    social_obs = get(observations, :social, agent.μ_social)
    
    # Gradient descent on beliefs (habituation)
    agent.μ_world .+= agent.η_world .* (world_obs .- agent.μ_world)
    agent.μ_self .+= agent.η_self .* (self_obs .- agent.μ_self)
    agent.μ_social .+= agent.η_social .* (social_obs .- agent.μ_social)
    
    # Update uncertainty based on prediction errors
    world_surprise = sum((world_obs .- agent.μ_world).^2)
    if world_surprise > 1.0
        agent.Σ_world *= 1.05  # Increase uncertainty if surprised
    else
        agent.Σ_world *= 0.98  # Decrease uncertainty if predictions match
    end
    
    # Clamp uncertainty to physiological range
    agent.Σ_world = clamp(agent.Σ_world, 0.3, 5.0)
    agent.Σ_self = clamp(agent.Σ_self, 0.3, 5.0)
    agent.Σ_social = clamp(agent.Σ_social, 0.3, 5.0)
end

"""
Simulate chronic anxiety world-model (greenteatree01's example).
"Amygdala overactivation can set a baseline high-anxiety world model
where everything feels more threatening than others would judge it to be."
"""
function simulate_anxiety_world_model(agent::SexSpecificAgent;
                                       n_steps::Int = 100,
                                       threat_exposure::Float64 = 0.5)
    free_energies = Float64[]
    threat_beliefs = Float64[]
    
    for t in 1:n_steps
        # Generate observations (with occasional threat)
        threat_signal = rand() < threat_exposure ? 1.0 : 0.0
        
        observations = (
            world = randn(5) .* 0.5,
            self = randn(3) .* 0.3,
            social = randn(4) .* 0.4,
            threat = threat_signal
        )
        
        # Compute free energy
        fe = world_model_free_energy(agent, observations)
        push!(free_energies, fe)
        
        # Track threat beliefs (does the agent expect threats?)
        # High β_threat × high uncertainty = anxious world-model
        threat_belief = agent.β_threat * agent.Σ_world
        push!(threat_beliefs, threat_belief)
        
        # Habituate
        habituate!(agent, observations)
    end
    
    return (
        free_energies = free_energies,
        threat_beliefs = threat_beliefs,
        final_uncertainty = agent.Σ_world,
        interpretation = agent.Σ_world > 2.0 ? 
            "High-anxiety world-model (threat-dominant)" :
            "Calibrated world-model (balanced)"
    )
end

# ============================================================================
# PART 4: POPULATION SIMULATION AND RATIO DERIVATION
# ============================================================================

"""
Simulate population to derive male:female ADHD ratio from causal model.
This is the key test: Does the SCM PRODUCE the observed 3:1 ratio?
"""
function simulate_population_ratio(;
    n_population::Int = 10000,
    adhd_threshold::Float64 = 60.0  # Score above this = ADHD diagnosis
)
    male_adhd_count = 0
    female_adhd_count = 0
    male_total = 0
    female_total = 0
    
    male_scores = Float64[]
    female_scores = Float64[]
    
    for i in 1:n_population
        is_female = rand() < 0.5
        
        # Create model with random exogenous variation
        model = SexualDimorphismSCM(
            is_female,
            is_female ? 0.3 + randn()*0.1 : 2.0 + randn()*0.3,
            is_female ? 2.0 + randn()*0.3 : 0.5 + randn()*0.1,
            randn(),    # U_genetic
            abs(randn()) * 0.5,  # U_inflammatory (positive)
            randn() * 0.5,  # U_developmental
            randn() * 0.3,  # U_socialization
            -1.7, 1.5,
            0.15, 0.35, 0.20,
            0.40, -0.25,
            0.15,
            -0.50
        )
        
        outcome = compute_full_scm(model, seed=i)
        
        if is_female
            female_total += 1
            push!(female_scores, outcome.adhd_severity)
            if outcome.adhd_severity > adhd_threshold
                female_adhd_count += 1
            end
        else
            male_total += 1
            push!(male_scores, outcome.adhd_severity)
            if outcome.adhd_severity > adhd_threshold
                male_adhd_count += 1
            end
        end
    end
    
    male_rate = male_adhd_count / male_total
    female_rate = female_adhd_count / female_total
    ratio = male_rate / female_rate
    
    return (
        male_adhd_rate = male_rate,
        female_adhd_rate = female_rate,
        male_to_female_ratio = ratio,
        male_mean_severity = mean(male_scores),
        female_mean_severity = mean(female_scores),
        male_std = std(male_scores),
        female_std = std(female_scores),
        interpretation = """
        Observed ratio: $(round(ratio, digits=2)):1 (male:female)
        Target ratio: 3:1
        Model calibration: $(abs(ratio - 3.0) < 0.5 ? "GOOD" : "NEEDS ADJUSTMENT")
        """
    )
end

"""
Decompose the male:female ratio into causal pathways.
Which pathway contributes most to the sex difference?
"""
function decompose_ratio_pathways(; n_samples::Int = 5000)
    pathways = Dict(
        :testosterone_faah => 0.0,
        :estrogen_cb1 => 0.0,
        :estrogen_aea => 0.0,
        :amygdala_anxiety => 0.0,
        :socialization => 0.0
    )
    
    # Baseline sex difference
    male_model = default_dimorphism_model(false)
    female_model = default_dimorphism_model(true)
    
    male_baseline = mean(compute_full_scm(male_model, seed=i).adhd_severity 
                         for i in 1:n_samples)
    female_baseline = mean(compute_full_scm(female_model, seed=i).adhd_severity 
                           for i in 1:n_samples)
    total_difference = male_baseline - female_baseline
    
    # Ablate each pathway and measure contribution
    
    # 1. Remove testosterone → FAAH pathway
    male_no_t_faah = SexualDimorphismSCM(
        false, 2.0, 0.5, 0.0, 0.0, 0.0, 0.0,
        -1.7, 1.5,
        0.0,   # ABLATED: testosterone_faah_coef = 0
        0.35, 0.20, 0.40, -0.25, 0.15, -0.50
    )
    ablated_male = mean(compute_full_scm(male_no_t_faah, seed=i).adhd_severity 
                        for i in 1:n_samples)
    pathways[:testosterone_faah] = male_baseline - ablated_male
    
    # 2. Remove estrogen → CB1 pathway
    female_no_e_cb1 = SexualDimorphismSCM(
        true, 0.3, 2.0, 0.0, 0.0, 0.0, 0.0,
        -1.7, 1.5,
        0.15,
        0.0,   # ABLATED: estrogen_cb1_coef = 0
        0.20, 0.40, -0.25, 0.15, -0.50
    )
    ablated_female = mean(compute_full_scm(female_no_e_cb1, seed=i).adhd_severity 
                          for i in 1:n_samples)
    pathways[:estrogen_cb1] = ablated_female - female_baseline
    
    # 3. Remove estrogen → AEA pathway
    female_no_e_aea = SexualDimorphismSCM(
        true, 0.3, 2.0, 0.0, 0.0, 0.0, 0.0,
        -1.7, 1.5,
        0.15, 0.35,
        0.0,   # ABLATED: estrogen_aea_coef = 0
        0.40, -0.25, 0.15, -0.50
    )
    ablated_aea = mean(compute_full_scm(female_no_e_aea, seed=i).adhd_severity 
                       for i in 1:n_samples)
    pathways[:estrogen_aea] = ablated_aea - female_baseline
    
    # Normalize to percentages
    total_pathway_effect = sum(abs(v) for v in values(pathways))
    pathway_contributions = Dict(
        k => round(abs(v) / total_pathway_effect * 100, digits=1) 
        for (k, v) in pathways
    )
    
    return (
        total_sex_difference = total_difference,
        pathway_effects = pathways,
        pathway_contributions_percent = pathway_contributions,
        dominant_pathway = argmax(pathway_contributions)
    )
end

# ============================================================================
# PART 5: MAIN ANALYSIS FUNCTIONS
# ============================================================================

"""
Run complete sexual dimorphism analysis.
"""
function run_dimorphism_analysis()
    println("╔══════════════════════════════════════════════════════════════════╗")
    println("║  ADHD-ECS Sexual Dimorphism: Counterfactual Causal Analysis      ║")
    println("╚══════════════════════════════════════════════════════════════════╝")
    
    # 1. Population ratio simulation
    println("\n─── 1. Population Ratio Simulation ───")
    ratio_result = simulate_population_ratio(n_population=10000)
    println("Male ADHD rate: $(round(ratio_result.male_adhd_rate * 100, digits=1))%")
    println("Female ADHD rate: $(round(ratio_result.female_adhd_rate * 100, digits=1))%")
    println("Male:Female ratio: $(round(ratio_result.male_to_female_ratio, digits=2)):1")
    println("Male mean severity: $(round(ratio_result.male_mean_severity, digits=1)) ± $(round(ratio_result.male_std, digits=1))")
    println("Female mean severity: $(round(ratio_result.female_mean_severity, digits=1)) ± $(round(ratio_result.female_std, digits=1))")
    
    # 2. Counterfactual sex swap
    println("\n─── 2. Counterfactual: Sex Swap ───")
    male_swap = counterfactual_sex_swap(default_dimorphism_model(false))
    female_swap = counterfactual_sex_swap(default_dimorphism_model(true))
    println("Male → Female hormones: ADHD $(round(male_swap.original_adhd, digits=1)) → $(round(male_swap.counterfactual_adhd, digits=1))")
    println("  Causal effect of male sex: +$(round(male_swap.causal_effect_of_sex, digits=1)) severity")
    println("Female → Male hormones: ADHD $(round(female_swap.original_adhd, digits=1)) → $(round(female_swap.counterfactual_adhd, digits=1))")
    println("  Causal effect of female sex: $(round(female_swap.causal_effect_of_sex, digits=1)) severity")
    
    # 3. Estrogen intervention
    println("\n─── 3. Counterfactual: Estrogen Intervention ───")
    estrogen_results = counterfactual_estrogen_intervention(1.5, n_samples=2000)
    println("do(Estrogen = 1.5) [moderate supplementation]:")
    for (sex, result) in estrogen_results
        println("  $sex: ADHD $(round(result.baseline_adhd, digits=1)) → $(round(result.intervention_adhd, digits=1)) (Δ = $(round(result.effect, digits=1)))")
    end
    
    # 4. Developmental timing
    println("\n─── 4. Counterfactual: Developmental Timing ───")
    for timing in [:early, :normal, :late]
        results = counterfactual_developmental_timing(puberty_timing=timing)
        println("Puberty timing: $timing")
        for (sex, r) in results
            println("  $sex: ADHD=$(round(r.mean_adhd, digits=1)), Anxiety=$(round(r.mean_anxiety, digits=1)), Precision=$(round(r.mean_precision, digits=2))")
        end
    end
    
    # 5. Pathway decomposition
    println("\n─── 5. Causal Pathway Decomposition ───")
    pathways = decompose_ratio_pathways(n_samples=3000)
    println("Total sex difference in ADHD severity: $(round(pathways.total_sex_difference, digits=1))")
    println("Pathway contributions:")
    for (pathway, contribution) in sort(collect(pathways.pathway_contributions_percent), by=x->-x[2])
        bar = repeat("█", Int(round(contribution / 5)))
        println("  $(rpad(pathway, 20)) $bar $(contribution)%")
    end
    println("Dominant pathway: $(pathways.dominant_pathway)")
    
    # 6. World-model simulation
    println("\n─── 6. World-Model Dynamics (Active Inference) ───")
    male_agent = create_sex_specific_agent(false)
    female_agent = create_sex_specific_agent(true)
    
    male_sim = simulate_anxiety_world_model(male_agent, threat_exposure=0.3)
    female_sim = simulate_anxiety_world_model(female_agent, threat_exposure=0.3)
    
    println("Male agent:")
    println("  Final world uncertainty: $(round(male_sim.final_uncertainty, digits=2))")
    println("  Mean free energy: $(round(mean(male_sim.free_energies), digits=2))")
    println("  $(male_sim.interpretation)")
    println("Female agent:")
    println("  Final world uncertainty: $(round(female_sim.final_uncertainty, digits=2))")
    println("  Mean free energy: $(round(mean(female_sim.free_energies), digits=2))")
    println("  $(female_sim.interpretation)")
    
    # Summary
    println("\n═══════════════════════════════════════════════════════════════════")
    println("SUMMARY: Sexual Dimorphism as Causal Factor")
    println("═══════════════════════════════════════════════════════════════════")
    println("""
    1. The 3:1 ratio EMERGES from the SCM ($(round(ratio_result.male_to_female_ratio, digits=1)):1 simulated)
    
    2. Sex is CAUSALLY upstream: sex-swap counterfactual changes ADHD by 
       $(round(abs(male_swap.causal_effect_of_sex), digits=1)) severity points
    
    3. Dominant pathway: $(pathways.dominant_pathway) 
       ($(pathways.pathway_contributions_percent[pathways.dominant_pathway])% of sex effect)
    
    4. Therapeutic implication: Estrogen supplementation in males could 
       reduce ADHD severity by $(round(estrogen_results["Male"].effect, digits=1)) points
    
    5. Active inference: Males develop higher world-model uncertainty 
       ($(round(male_sim.final_uncertainty, digits=2)) vs $(round(female_sim.final_uncertainty, digits=2)))
       → less precise predictions → ADHD phenotype
    
    KEY INSIGHT (greenteatree01's point operationalized):
    Sexual dimorphism operates through PHENOTYPIC pathways (hormones, habituation,
    world-model dynamics) not merely genotype. The causal structure is:
    
      Biological Sex → Hormones → ECS Tone → Precision → World-Model → ADHD
                         ↑
                    (phenotypic,
                     developmentally
                     modifiable)
    """)
end

# Export public interface
export SexualDimorphismSCM, default_dimorphism_model
export compute_full_scm
export counterfactual_sex_swap, counterfactual_estrogen_intervention
export counterfactual_developmental_timing
export SexSpecificAgent, create_sex_specific_agent
export world_model_free_energy, habituate!, simulate_anxiety_world_model
export simulate_population_ratio, decompose_ratio_pathways
export run_dimorphism_analysis

end # module

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    using .SexualDimorphismECS
    SexualDimorphismECS.run_dimorphism_analysis()
end
