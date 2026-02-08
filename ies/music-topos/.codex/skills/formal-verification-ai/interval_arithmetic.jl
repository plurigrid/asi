"""
Interval Arithmetic for Neural Network Verification

Implements interval propagation through neural networks to compute
certified bounds on outputs and verify robustness properties.
"""

module IntervalArithmeticModule

export Interval, propagate_interval, verify_robustness
export interval_add, interval_mul, interval_relu, interval_affine

using LinearAlgebra

"""
Multi-dimensional interval: [lower, upper] for each dimension
"""
struct Interval
    lower::Vector{Float64}
    upper::Vector{Float64}

    function Interval(lower::Vector{Float64}, upper::Vector{Float64})
        @assert length(lower) == length(upper) "Dimension mismatch"
        @assert all(lower .<= upper) "Invalid interval: lower > upper"
        new(lower, upper)
    end
end

# Convenience constructor for scalar intervals
Interval(l::Float64, u::Float64) = Interval([l], [u])

"""
Interval addition: [a, b] + [c, d] = [a+c, b+d]
"""
function interval_add(I1::Interval, I2::Interval)
    return Interval(I1.lower + I2.lower, I1.upper + I2.upper)
end

"""
Interval scalar multiplication: α * [a, b]
"""
function interval_scale(α::Float64, I::Interval)
    if α >= 0
        return Interval(α * I.lower, α * I.upper)
    else
        return Interval(α * I.upper, α * I.lower)
    end
end

"""
Interval matrix multiplication: W * [x_l, x_u]
"""
function interval_matvec(W::Matrix{Float64}, I::Interval)
    m, n = size(W)
    @assert n == length(I.lower) "Dimension mismatch"

    lower = zeros(m)
    upper = zeros(m)

    for i in 1:m
        # For each output dimension, compute bounds
        for j in 1:n
            if W[i, j] >= 0
                lower[i] += W[i, j] * I.lower[j]
                upper[i] += W[i, j] * I.upper[j]
            else
                lower[i] += W[i, j] * I.upper[j]
                upper[i] += W[i, j] * I.lower[j]
            end
        end
    end

    return Interval(lower, upper)
end

"""
Interval ReLU: ReLU([a, b]) = [max(0, a), max(0, b)]
"""
function interval_relu(I::Interval)
    lower = max.(0.0, I.lower)
    upper = max.(0.0, I.upper)
    return Interval(lower, upper)
end

"""
Interval affine transformation: W*x + b
"""
function interval_affine(W::Matrix{Float64}, b::Vector{Float64}, I::Interval)
    result = interval_matvec(W, I)
    return interval_add(result, Interval(b, b))
end

"""
Propagate interval through single layer
"""
function propagate_layer(W::Matrix{Float64}, b::Vector{Float64}, I::Interval, activation::Symbol)
    # Affine transform
    result = interval_affine(W, b, I)

    # Activation
    if activation == :relu
        return interval_relu(result)
    elseif activation == :linear
        return result
    elseif activation == :tanh
        # Approximate tanh bounds
        return interval_tanh(result)
    else
        error("Unsupported activation: $activation")
    end
end

"""
Interval tanh (conservative approximation)
"""
function interval_tanh(I::Interval)
    # tanh is monotonic, so just apply to bounds
    lower = tanh.(I.lower)
    upper = tanh.(I.upper)
    return Interval(lower, upper)
end

"""
Propagate interval through multi-layer network
"""
function propagate_interval(layers::Vector, input_interval::Interval)
    current = input_interval

    for layer in layers
        # Assume layer is (W, b, activation)
        W, b, activation = layer
        current = propagate_layer(W, b, current, activation)
    end

    return current
end

"""
Verify robustness: for all x in input_interval, f(x) has same classification
"""
function verify_robustness(layers::Vector, input_interval::Interval, true_class::Int)
    output_interval = propagate_interval(layers, input_interval)

    # Check if true_class always has highest value
    n_classes = length(output_interval.lower)

    # True class lower bound
    true_lower = output_interval.lower[true_class]

    # Check against all other classes' upper bounds
    for c in 1:n_classes
        if c != true_class
            if output_interval.upper[c] >= true_lower
                # Possible misclassification
                return false
            end
        end
    end

    return true
end

"""
Compute epsilon-ball interval around point
"""
function epsilon_ball(x::Vector{Float64}, epsilon::Float64, norm_type::Symbol=:linf)
    if norm_type == :linf
        return Interval(x .- epsilon, x .+ epsilon)
    elseif norm_type == :l2
        # L2 ball is harder to represent exactly; use box approximation
        return Interval(x .- epsilon, x .+ epsilon)
    else
        error("Unsupported norm: $norm_type")
    end
end

"""
Tighten interval using optimization (abstract interpretation)
"""
function tighten_interval(I::Interval, constraint::Function)
    # Placeholder for more sophisticated abstract interpretation
    # Would use LP/QP to tighten bounds given constraints
    return I
end

end  # module
