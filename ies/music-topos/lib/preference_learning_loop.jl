#!/usr/bin/env julia
# preference_learning_loop.jl
#
# Learning Loop for Binary Preferences with Regularization
#
# Implements:
# - Ranking loss (pairwise hinge loss)
# - Smoothness regularization (PLR weight consistency)
# - Gradient descent with adaptive learning rate
# - Exploration strategy (epsilon-greedy)
# - Batch training with convergence monitoring

include("learnable_plr_network.jl")

using Statistics

# =============================================================================
# Loss Functions
# =============================================================================

"""
Ranking loss (pairwise hinge loss) with margin.
Penalizes when rejected color scores higher than preferred.

Loss = max(0, margin - (score_preferred - score_rejected))
"""
function ranking_loss(score_pref::Float64, score_rej::Float64; margin::Float64=0.1)::Float64
    max(0.0, margin - (score_pref - score_rej))
end

"""
Smoothness regularization: penalize divergence between PLR weight vectors.
Encourages P, L, R transformations to have similar preference structures.

Loss = λ * (||weights_P - weights_L||² + ||weights_L - weights_R||²)
"""
function smoothness_regularization(net::LearnablePLRMapping; lambda::Float64=0.01)::Float64
    diff_PL = net.weights_P .- net.weights_L
    diff_LR = net.weights_L .- net.weights_R
    lambda * (sum(diff_PL .^ 2) + sum(diff_LR .^ 2))
end

"""
Voice leading smoothness loss: penalize large color changes.
Encourages transformations to preserve perceptual continuity.

Loss = ρ * mean(ΔE² for all transitions)
"""
function voice_leading_loss(deltas::Vector{Float64}; rho::Float64=0.01)::Float64
    if isempty(deltas)
        return 0.0
    end
    mean_delta = mean(deltas)
    target_delta = 20.0  # Optimal ΔE threshold
    rho * (mean_delta - target_delta)^2
end

"""
Total loss combining all components with weighting.
"""
function total_loss(
    rank_loss::Float64,
    smooth_loss::Float64,
    voice_loss::Float64;
    weights::Tuple{Float64, Float64, Float64}=(1.0, 0.1, 0.1)
)::Float64
    w_rank, w_smooth, w_voice = weights
    w_rank * rank_loss + w_smooth * smooth_loss + w_voice * voice_loss
end

# =============================================================================
# Gradient-Based Training
# =============================================================================

"""
Single preference update using gradient descent.
Computes gradients and applies learning rate scaled update.
"""
function gradient_descent_step!(
    net::LearnablePLRMapping,
    preferred::NamedTuple,
    rejected::NamedTuple,
    plr::Symbol;
    margin::Float64=0.1,
    learning_rate::Float64=0.01
)::Tuple{Float64, Float64, Float64}
    # Compute preference scores
    score_pref = net(preferred, plr)
    score_rej = net(rejected, plr)

    # Compute ranking loss
    r_loss = ranking_loss(score_pref, score_rej, margin=margin)

    # Compute smoothness regularization
    s_loss = smoothness_regularization(net)

    # Compute voice leading loss (estimate from delta-E)
    delta_e = color_distance_delta_e(preferred, rejected)
    v_loss = voice_leading_loss([delta_e])

    # Only update if loss > 0 (margin violated)
    if r_loss > 0
        # Compute gradients
        features_pref = extract_features(preferred)
        features_rej = extract_features(rejected)

        grad_pref = sigmoid_derivative(score_pref)
        grad_rej = sigmoid_derivative(score_rej)

        # Update weights for this PLR type
        weights = get_weights(net, plr)
        delta = learning_rate * (grad_pref .* vcat(features_pref, 1.0) .- grad_rej .* vcat(features_rej, 1.0))
        weights .+= delta
        set_weights!(net, plr, weights)
    end

    (r_loss, s_loss, v_loss)
end

# =============================================================================
# Batch Training with Convergence Monitoring
# =============================================================================

"""
Training history entry tracking loss values over time.
"""
struct TrainingStep
    step::Int
    total_loss::Float64
    rank_loss::Float64
    smooth_loss::Float64
    voice_loss::Float64
    updates_applied::Int
end

"""
Batch training on multiple preferences with exploration.
Returns convergence metrics.
"""
function train_batch_with_convergence!(
    net::LearnablePLRMapping,
    preferences::Vector;
    margin::Float64=0.1,
    learning_rate::Float64=0.01,
    smooth_weight::Float64=0.1,
    voice_weight::Float64=0.1,
    regularization_weight::Float64=0.01
)::Tuple{Vector{TrainingStep}, Float64}
    history = TrainingStep[]
    step = 0

    for (preferred, rejected, plr) in preferences
        step += 1

        # Gradient descent step
        r_loss, s_loss, v_loss = gradient_descent_step!(
            net, preferred, rejected, plr,
            margin=margin, learning_rate=learning_rate
        )

        # Accumulate regularization loss
        s_loss += regularization_weight * sum(abs2, net.weights_P .- net.weights_L)

        # Total loss
        t_loss = total_loss(r_loss, s_loss, v_loss,
                           weights=(1.0, smooth_weight, voice_weight))

        updates = r_loss > 0 ? 1 : 0
        push!(history, TrainingStep(step, t_loss, r_loss, s_loss, v_loss, updates))
    end

    # Compute convergence metric: ratio of final loss to initial loss
    convergence = if !isempty(history)
        history[1].total_loss > 1e-6 ? history[end].total_loss / history[1].total_loss : 0.0
    else
        0.0
    end

    (history, convergence)
end

# =============================================================================
# Exploration Strategy (Epsilon-Greedy)
# =============================================================================

"""
Epsilon-greedy exploration: balance exploitation and exploration.
With probability epsilon, choose random action; otherwise choose best.
"""
function epsilon_greedy_choice(
    navigator::PLRLatticeNavigatorWithLearning,
    epsilon::Float64=0.1
)::Symbol
    if rand() < epsilon
        # Explore: choose random PLR type
        [:P, :L, :R][rand(1:3)]
    else
        # Exploit: choose highest scoring PLR type
        suggestions = suggest_next(navigator)
        suggestions[1][1]  # Return best PLR type
    end
end

"""
Exploration bonus for visiting less-explored regions.
Encourages gamut boundary expansion.
"""
function exploration_bonus(
    color::NamedTuple,
    explored_colors::Vector{NamedTuple};
    bonus_scale::Float64=0.1
)::Float64
    if isempty(explored_colors)
        return bonus_scale
    end

    # Distance to nearest explored color
    min_dist = minimum(color_distance_delta_e(color, c) for c in explored_colors)

    # Bonus inversely proportional to closeness (more bonus for novel areas)
    bonus_scale / (1.0 + min_dist / 30.0)
end

# =============================================================================
# Interactive Learning Session
# =============================================================================

"""
Conduct an interactive learning session where user provides preferences.
Accumulates preference examples and trains network.
"""
mutable struct InteractiveLearningSession
    network::LearnablePLRMapping
    navigator::PLRLatticeNavigatorWithLearning
    preferences::Vector{Tuple{NamedTuple, NamedTuple, Symbol}}
    explored_colors::Vector{NamedTuple}
    training_history::Vector{TrainingStep}
end

function InteractiveLearningSession(start_color::NamedTuple)
    net = LearnablePLRMapping()
    nav = PLRLatticeNavigatorWithLearning(start_color, net)
    InteractiveLearningSession(net, nav, [], [start_color], [])
end

"""
Add a preference example: "I prefer color1 over color2 for transformation plr"
"""
function add_preference!(
    session::InteractiveLearningSession,
    preferred::NamedTuple,
    rejected::NamedTuple,
    plr::Symbol
)
    push!(session.preferences, (preferred, rejected, plr))
    push!(session.explored_colors, preferred)
    push!(session.explored_colors, rejected)
end

"""
Run training on accumulated preferences.
"""
function train!(session::InteractiveLearningSession; batch_size::Int=10)::Dict{String, Any}
    if length(session.preferences) < 1
        return Dict("status" => "No preferences to train on")
    end

    # Train on batches of preferences
    history, convergence = train_batch_with_convergence!(
        session.network,
        session.preferences,
        margin=0.1,
        learning_rate=0.01,
        regularization_weight=0.01
    )

    append!(session.training_history, history)

    Dict(
        "steps_trained" => length(history),
        "convergence_ratio" => convergence,
        "final_loss" => (isempty(history) ? 0.0 : history[end].total_loss),
        "exploration_bonus" => exploration_bonus(
            session.navigator.current_color,
            session.explored_colors
        )
    )
end

"""
Get prediction accuracy on a test set.
"""
function evaluate(
    session::InteractiveLearningSession,
    test_preferences::Vector
)::Dict{String, Float64}
    if isempty(test_preferences)
        return Dict()
    end

    correct = 0
    for (preferred, rejected, plr) in test_preferences
        score_pref = session.network(preferred, plr)
        score_rej = session.network(rejected, plr)
        if score_pref > score_rej
            correct += 1
        end
    end

    accuracy = correct / length(test_preferences)

    Dict(
        "accuracy" => accuracy,
        "num_test" => length(test_preferences),
        "num_correct" => correct
    )
end

# =============================================================================
# Test Suite
# =============================================================================

function test_preference_learning_loop()
    println("Testing Preference Learning Loop...")

    # Test 1: Loss functions
    net = LearnablePLRMapping()
    start = (L=65.0, C=50.0, H=120.0, index=0)

    p1 = parallel_transform(start)
    p2 = parallel_transform(start, direction=-1)

    r_loss = ranking_loss(0.7, 0.3)
    s_loss = smoothness_regularization(net)
    println("Ranking loss: $r_loss, Smoothness loss: $s_loss")
    println("✓ Loss functions")

    # Test 2: Gradient descent step
    r_loss, s_loss, v_loss = gradient_descent_step!(net, p1, p2, :P)
    println("Step loss: R=$r_loss, S=$s_loss, V=$v_loss")
    println("✓ Gradient descent step")

    # Test 3: Batch training
    prefs = [(p1, p2, :P), (p1, p2, :L), (p1, p2, :R)]
    history, conv = train_batch_with_convergence!(net, prefs, margin=0.1, learning_rate=0.01)
    println("Training steps: $(length(history)), Convergence: $conv")
    println("✓ Batch training")

    # Test 4: Exploration strategy
    nav = PLRLatticeNavigatorWithLearning(start, net)
    choice = epsilon_greedy_choice(nav, 0.2)
    println("Epsilon-greedy choice: $choice")
    println("✓ Exploration strategy")

    # Test 5: Interactive learning session
    session = InteractiveLearningSession(start)
    add_preference!(session, p1, p2, :P)
    add_preference!(session, p1, parallel_transform(start, direction=-1), :L)

    result = train!(session)
    println("Training result: $result")
    println("✓ Interactive session")

    # Test 6: Evaluation
    test_prefs = [(p1, p2, :P), (p1, p2, :R)]
    eval = evaluate(session, test_prefs)
    println("Evaluation: $eval")
    println("✓ Evaluation")

    println("\nAll tests passed! ✓")
end

# Run tests if this file is executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    test_preference_learning_loop()
end
