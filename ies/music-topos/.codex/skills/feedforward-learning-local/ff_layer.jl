"""
Forward-Forward Layer Implementation

Implements Hinton's forward-forward algorithm with local goodness functions
and layer-wise contrastive learning.
"""

module FFLayerModule

export FFLayer, goodness, train_step!, forward

using LinearAlgebra
using Statistics

"""
Forward-Forward Layer
"""
mutable struct FFLayer
    input_dim::Int
    hidden_dim::Int

    # Weights and biases
    W::Matrix{Float64}
    b::Vector{Float64}

    # Goodness threshold
    threshold::Float64

    # Learning rate
    lr::Float64

    # Normalization statistics
    running_mean::Vector{Float64}
    running_var::Vector{Float64}
    momentum::Float64

    function FFLayer(; input_dim::Int, hidden_dim::Int, threshold::Float64=2.0, lr::Float64=0.03)
        W = randn(hidden_dim, input_dim) * sqrt(2.0 / input_dim)
        b = zeros(hidden_dim)
        running_mean = zeros(hidden_dim)
        running_var = ones(hidden_dim)

        new(input_dim, hidden_dim, W, b, threshold, lr, running_mean, running_var, 0.9)
    end
end

"""
Forward pass with ReLU activation
"""
function forward(layer::FFLayer, x::Vector{Float64}; normalize::Bool=true)
    # Linear transform
    z = layer.W * x + layer.b

    # ReLU activation
    h = max.(z, 0.0)

    # Layer normalization (optional)
    if normalize
        h = (h .- layer.running_mean) ./ sqrt.(layer.running_var .+ 1e-8)
    end

    return h
end

function forward(layer::FFLayer, X::Matrix{Float64}; normalize::Bool=true)
    # Batch forward pass
    H = similar(X, layer.hidden_dim, size(X, 2))

    for i in 1:size(X, 2)
        H[:, i] = forward(layer, X[:, i]; normalize=normalize)
    end

    return H
end

"""
Goodness function: sum of squared activities
"""
function goodness(layer::FFLayer, x::Vector{Float64})
    h = forward(layer, x; normalize=false)
    return sum(h .^ 2)
end

"""
Training step: contrastive learning on positive/negative data
"""
function train_step!(layer::FFLayer, x_pos::Vector{Float64}, x_neg::Vector{Float64})
    # Forward pass for positive and negative
    h_pos = forward(layer, x_pos; normalize=false)
    h_neg = forward(layer, x_neg; normalize=false)

    # Compute goodness
    g_pos = sum(h_pos .^ 2)
    g_neg = sum(h_neg .^ 2)

    # Update running statistics
    update_statistics!(layer, h_pos)

    # Gradient of goodness with respect to W
    # Want to increase g_pos and decrease g_neg

    # Positive gradient (increase goodness)
    if g_pos < layer.threshold
        # ∇_W g = 2 h h^T, ∇_W h = diag(h > 0) W, ∇_z h = diag(h > 0)
        # ∇_W g = 2 h (∇_W h) = 2 h x^T where h = σ(Wx + b)
        dW_pos = 2.0 * h_pos * x_pos'
        db_pos = 2.0 * h_pos
    else
        dW_pos = zeros(size(layer.W))
        db_pos = zeros(size(layer.b))
    end

    # Negative gradient (decrease goodness)
    if g_neg > layer.threshold
        dW_neg = -2.0 * h_neg * x_neg'
        db_neg = -2.0 * h_neg
    else
        dW_neg = zeros(size(layer.W))
        db_neg = zeros(size(layer.b))
    end

    # Update weights
    layer.W += layer.lr * (dW_pos + dW_neg)
    layer.b += layer.lr * (db_pos + db_neg)

    return (g_pos=g_pos, g_neg=g_neg)
end

"""
Update running statistics for normalization
"""
function update_statistics!(layer::FFLayer, h::Vector{Float64})
    layer.running_mean = layer.momentum * layer.running_mean + (1 - layer.momentum) * h
    layer.running_var = layer.momentum * layer.running_var + (1 - layer.momentum) * (h .^ 2)
end

"""
Generate negative data by overlaying wrong label
"""
function overlay_wrong_label(x::Vector{Float64}, correct_label::Int, n_classes::Int=10)
    # Assume first n_classes dimensions encode label as one-hot
    x_neg = copy(x)

    # Zero out correct label
    x_neg[correct_label] = 0.0

    # Set random wrong label
    wrong_label = mod(correct_label + rand(1:(n_classes-1)), n_classes)
    x_neg[wrong_label == 0 ? n_classes : wrong_label] = 1.0

    return x_neg
end

"""
Alternative: add noise as negative data
"""
function add_noise_negative(x::Vector{Float64}, noise_level::Float64=0.1)
    return x + noise_level * randn(length(x))
end

"""
Batch training step
"""
function train_step!(layer::FFLayer, X_pos::Matrix{Float64}, X_neg::Matrix{Float64})
    n_samples = size(X_pos, 2)
    total_g_pos = 0.0
    total_g_neg = 0.0

    for i in 1:n_samples
        result = train_step!(layer, X_pos[:, i], X_neg[:, i])
        total_g_pos += result.g_pos
        total_g_neg += result.g_neg
    end

    return (avg_g_pos=total_g_pos/n_samples, avg_g_neg=total_g_neg/n_samples)
end

end  # module
