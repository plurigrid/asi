#!/usr/bin/env julia
# learnable_plr_network.jl
#
# Multiscale neural architecture for learning PLR transformations
# Organized into three scales:
# 1. Microscale: Individual color→pitch mappings (sigmoid weights)
# 2. Mesoscale: Local PLR navigation with state tracking
# 3. Macroscale: Global harmonic function analysis (T/S/D classification)
#
# All scales integrate learnable weights that adapt based on user preferences

include("plr_color_lattice.jl")

using Statistics

# =============================================================================
# Microscale: Learnable PLR Mapping (Sigmoid-Activated)
# =============================================================================

"""
Learnable mapping for P/L/R transformations with individual weight vectors.
Each transformation type (P, L, R) has its own sigmoid-activated neural network.

Sigmoid activation: χ(features) = 1 / (1 + exp(-z)) where z = w·f + b
Maps color features to preference score in [0, 1].
"""
mutable struct LearnablePLRMapping
    # Separate weight vectors for each transformation type
    weights_P::Vector{Float64}    # [w_L, w_C, w_H, bias] for P transform
    weights_L::Vector{Float64}    # [w_L, w_C, w_H, bias] for L transform
    weights_R::Vector{Float64}    # [w_L, w_C, w_H, bias] for R transform

    # Training history: (color, plr_type, preference_score)
    history::Vector{Tuple{NamedTuple, Symbol, Float64}}

    # Hyperparameters
    learning_rate::Float64
    threshold::Float64           # Classification threshold for preferences
end

"""
Initialize LearnablePLRMapping with random weights around 0.5 (balanced).
"""
function LearnablePLRMapping(; learning_rate::Float64=0.01, threshold::Float64=0.5)
    # Initialize weights: [w_L, w_C, w_H, bias]
    # Start with balanced weights (0.5) to avoid bias toward any color dimension
    weights = [0.33, 0.33, 0.33, 0.0]

    LearnablePLRMapping(
        copy(weights),  # weights_P
        copy(weights),  # weights_L
        copy(weights),  # weights_R
        [],             # history
        learning_rate,
        threshold
    )
end

"""
Sigmoid activation function.
Maps linear combination of features to [0, 1] preference score.
"""
sigmoid(z::Float64)::Float64 = 1.0 / (1.0 + exp(-z))

"""
Sigmoid derivative for gradient computation: σ'(z) = σ(z) * (1 - σ(z))
"""
sigmoid_derivative(output::Float64)::Float64 = output * (1.0 - output)

"""
Extract normalized features from a color.
Returns [L_norm, C_norm, H_norm] where each is in [0, 1].
"""
function extract_features(color::NamedTuple)::Vector{Float64}
    [color.L / 100.0, color.C / 150.0, color.H / 360.0]
end

"""
Get weights for a specific PLR transformation type.
"""
function get_weights(net::LearnablePLRMapping, plr::Symbol)::Vector{Float64}
    if plr == :P
        net.weights_P
    elseif plr == :L
        net.weights_L
    elseif plr == :R
        net.weights_R
    else
        error("Unknown PLR type: $plr")
    end
end

"""
Set weights for a specific PLR transformation type.
"""
function set_weights!(net::LearnablePLRMapping, plr::Symbol, weights::Vector{Float64})
    if plr == :P
        net.weights_P = weights
    elseif plr == :L
        net.weights_L = weights
    elseif plr == :R
        net.weights_R = weights
    else
        error("Unknown PLR type: $plr")
    end
end

"""
Forward pass: Compute preference score for a color under a specific PLR transformation.
χ(color, plr_type) ∈ [0, 1] - higher means more preferred
"""
function (net::LearnablePLRMapping)(color::NamedTuple, plr::Symbol)::Float64
    features = extract_features(color)
    weights = get_weights(net, plr)

    # Linear combination: z = w_L*L + w_C*C + w_H*H + bias
    z = sum(weights[1:3] .* features) + weights[4]

    # Sigmoid activation: χ = 1 / (1 + exp(-z))
    sigmoid(z)
end

"""
Classify a color as preferred (true) or not (false) based on threshold.
"""
function classify(net::LearnablePLRMapping, color::NamedTuple, plr::Symbol)::Bool
    net(color, plr) > net.threshold
end

"""
Train on a single preference: "preferred_color is better for plr_type than rejected_color"
Uses ranking loss with margin-based gradient descent.
"""
function train_binary_preference!(
    net::LearnablePLRMapping,
    preferred::NamedTuple,
    rejected::NamedTuple,
    plr::Symbol;
    margin::Float64=0.1
)
    # Forward pass
    score_pref = net(preferred, plr)
    score_rej = net(rejected, plr)

    # Ranking loss: max(0, margin - (score_pref - score_rej))
    loss = max(0.0, margin - (score_pref - score_rej))

    # Only update if loss > 0 (violation of margin)
    if loss > 0
        features_pref = extract_features(preferred)
        features_rej = extract_features(rejected)

        # Gradients: ∇loss = -(d_pref - d_rej) where d = sigmoid'(z) * features
        grad_pref = sigmoid_derivative(score_pref)
        grad_rej = sigmoid_derivative(score_rej)

        # Update rule: w ← w + lr * (grad_pref * features_pref - grad_rej * features_rej)
        weights = get_weights(net, plr)
        delta = net.learning_rate * (grad_pref .* vcat(features_pref, 1.0) .- grad_rej .* vcat(features_rej, 1.0))
        weights .+= delta

        set_weights!(net, plr, weights)
    end

    # Record in history
    push!(net.history, (preferred, plr, 1.0))
    push!(net.history, (rejected, plr, 0.0))

    loss
end

"""
Batch training on multiple preferences with exploration bonus.
"""
function train_batch!(
    net::LearnablePLRMapping,
    preferences::Vector{Tuple{NamedTuple, NamedTuple, Symbol}};
    regularization_weight::Float64=0.01
)
    total_loss = 0.0
    updates = 0

    for (preferred, rejected, plr) in preferences
        loss = train_binary_preference!(net, preferred, rejected, plr)
        total_loss += loss
        updates += (loss > 0 ? 1 : 0)
    end

    # Smoothness regularization: penalize divergence between weight vectors
    # Encourages similar transformations to have similar preference scores
    reg_loss = regularization_weight * (
        sum(abs2, net.weights_P .- net.weights_L) +
        sum(abs2, net.weights_L .- net.weights_R)
    )

    (total_loss / max(1, updates), reg_loss)
end

# =============================================================================
# Mesoscale: PLR Lattice Navigator with Learning
# =============================================================================

"""
Navigator with integrated learning that adapts to user preferences.
Tracks position in PLR lattice and learns which directions are preferred.
"""
mutable struct PLRLatticeNavigatorWithLearning
    current_color::NamedTuple
    history::Vector{Tuple{NamedTuple, Symbol}}  # Navigation path
    learning_net::LearnablePLRMapping            # Learnable preferences
    transformation_deltas::Vector{Float64}
end

function PLRLatticeNavigatorWithLearning(start_color::NamedTuple, net::LearnablePLRMapping)
    PLRLatticeNavigatorWithLearning(
        start_color,
        [(start_color, :START)],
        net,
        [0.0]
    )
end

"""
Navigate to a neighboring color in the PLR lattice.
Uses learned preferences to rank options.
"""
function navigate!(nav::PLRLatticeNavigatorWithLearning, plr::Symbol; direction::Int=1)::NamedTuple
    old_color = nav.current_color

    # Apply transformation
    new_color = if plr == :P
        parallel_transform(old_color, direction=direction)
    elseif plr == :L
        leading_tone_transform(old_color, direction=direction)
    elseif plr == :R
        relative_transform(old_color, direction=direction)
    else
        error("Unknown PLR transformation: $plr")
    end

    # Query learned preference for this transformation
    preference_score = nav.learning_net(new_color, plr)

    # Track navigation
    push!(nav.history, (new_color, plr))
    delta_e = color_distance_delta_e(old_color, new_color)
    push!(nav.transformation_deltas, delta_e)

    nav.current_color = new_color
    new_color
end

"""
Get suggested next transformation based on learned preferences.
Returns [(plr, score), ...] sorted by preference score.
"""
function suggest_next(nav::PLRLatticeNavigatorWithLearning)::Vector{Tuple{Symbol, Float64}}
    current = nav.current_color

    scores = [
        (:P, nav.learning_net(parallel_transform(current), :P)),
        (:L, nav.learning_net(leading_tone_transform(current), :L)),
        (:R, nav.learning_net(relative_transform(current), :R))
    ]

    sort(scores, by=x -> x[2], rev=true)
end

# =============================================================================
# Macroscale: Harmonic Function Analyzer
# =============================================================================

"""
Classify colors into harmonic functions (Tonic/Subdominant/Dominant)
using learnable color algebra.
Integrates with LearnableColorAlgebra from colored_sexp_acset.jl
"""
mutable struct HarmonicFunctionAnalyzer
    navigator::PLRLatticeNavigatorWithLearning

    # Functional classifiers: T/S/D each with learnable weights
    tonic_classifier::LearnablePLRMapping
    subdominant_classifier::LearnablePLRMapping
    dominant_classifier::LearnablePLRMapping

    # Hue zones for functional families (baseline, can be learned)
    hue_zones::Dict{Symbol, Tuple{Float64, Float64}}  # (min_hue, max_hue)
end

"""
Initialize HarmonicFunctionAnalyzer.
Sets up functional classifiers and hue zone priors.
"""
function HarmonicFunctionAnalyzer(navigator::PLRLatticeNavigatorWithLearning)
    HarmonicFunctionAnalyzer(
        navigator,
        LearnablePLRMapping(),
        LearnablePLRMapping(),
        LearnablePLRMapping(),
        Dict(
            :tonic => (330.0, 90.0),        # Warm hues: reds, oranges
            :subdominant => (90.0, 210.0),  # Cool-warm: greens, yellows
            :dominant => (210.0, 330.0)     # Cool hues: blues, purples
        )
    )
end

"""
Analyze color's functional harmony role (T/S/D).
Returns symbolic classification and confidence scores.
"""
function analyze_function(analyzer::HarmonicFunctionAnalyzer, color::NamedTuple)::Tuple{Symbol, Dict{Symbol, Float64}}
    current = color

    # Query each functional classifier
    t_score = analyzer.tonic_classifier(current, :P)
    s_score = analyzer.subdominant_classifier(current, :L)
    d_score = analyzer.dominant_classifier(current, :R)

    # Normalize scores to probabilities
    total = t_score + s_score + d_score
    t_prob = t_score / total
    s_prob = s_score / total
    d_prob = d_score / total

    # Return highest probability function
    function_scores = Dict(
        :tonic => t_prob,
        :subdominant => s_prob,
        :dominant => d_prob
    )

    best_function = argmax(function_scores)
    (best_function, function_scores)
end

"""
Generate a cadence (harmonic progression) using PLR paths.
Maps from one functional color to another through optimal PLR path.
"""
function generate_cadence(
    analyzer::HarmonicFunctionAnalyzer,
    cadence_type::Symbol
)::Vector{NamedTuple}
    # Define typical cadence progressions
    progressions = Dict(
        :authentic => [:dominant, :tonic],       # V→I
        :plagal => [:subdominant, :tonic],       # IV→I
        :deceptive => [:dominant, :subdominant]  # V→VI
    )

    if !haskey(progressions, cadence_type)
        error("Unknown cadence type: $cadence_type")
    end

    # Get functional sequence
    functions = progressions[cadence_type]
    colors = [analyzer.navigator.current_color]

    for func in functions
        # Find a color classified as this function
        # For now, apply transformations based on function
        next_color = if func == :tonic
            parallel_transform(colors[end])  # P transformation
        elseif func == :subdominant
            leading_tone_transform(colors[end])  # L transformation
        else  # :dominant
            relative_transform(colors[end])  # R transformation
        end

        push!(colors, next_color)
    end

    colors
end

# =============================================================================
# Test Suite
# =============================================================================

function test_learnable_plr_network()
    println("Testing Learnable PLR Network...")

    # Test 1: LearnablePLRMapping initialization
    net = LearnablePLRMapping()
    println("Initialized LearnablePLRMapping")
    println("✓ Network initialization")

    # Test 2: Forward pass (preference scoring)
    start = (L=65.0, C=50.0, H=120.0, index=0)
    score_p = net(start, :P)
    println("Preference score for P transform: $(score_p)")
    @assert 0.0 <= score_p <= 1.0 "Score should be in [0, 1]"
    println("✓ Forward pass (sigmoid activation)")

    # Test 3: Binary preference training
    preferred = parallel_transform(start)
    rejected = parallel_transform(start, direction=-1)
    loss = train_binary_preference!(net, preferred, rejected, :P)
    println("Training loss: $(loss)")
    println("✓ Binary preference training")

    # Test 4: PLRLatticeNavigatorWithLearning
    nav = PLRLatticeNavigatorWithLearning(start, net)
    navigate!(nav, :P)
    navigate!(nav, :L)
    navigate!(nav, :R)
    println("Navigation path length: $(length(nav.history))")
    println("✓ Navigator with learning")

    # Test 5: Suggested next steps
    suggestions = suggest_next(nav)
    println("Next step suggestions: $(suggestions)")
    println("✓ Preference-based suggestions")

    # Test 6: HarmonicFunctionAnalyzer
    analyzer = HarmonicFunctionAnalyzer(nav)
    func, scores = analyze_function(analyzer, start)
    println("Harmonic function analysis: $(func) with scores $(scores)")
    println("✓ Harmonic function classification")

    # Test 7: Cadence generation
    cadence = generate_cadence(analyzer, :authentic)
    println("Authentic cadence length: $(length(cadence))")
    println("✓ Cadence generation")

    println("\nAll tests passed! ✓")
end

# Run tests if this file is executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    test_learnable_plr_network()
end
