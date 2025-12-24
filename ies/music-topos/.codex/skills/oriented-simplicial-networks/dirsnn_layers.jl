"""
Directional Simplicial Neural Network Layers

Implements asymmetric message passing on oriented simplicial complexes
with E(n)-equivariant operations.
"""

module DirSNNLayers

export SimplicialConv, SimplicialPooling, DirSNN
export forward_pass, compute_messages

using LinearAlgebra
include("simplicial_complex.jl")
using .SimplicialComplexModule

"""
Directional Simplicial Convolution Layer
"""
struct SimplicialConv
    dimension::Int  # Which dimension of simplices this operates on
    in_features::Int
    out_features::Int

    # Asymmetric weight matrices for up/down message passing
    W_up::Matrix{Float64}
    W_down::Matrix{Float64}
    W_self::Matrix{Float64}

    # Bias and activation
    bias::Vector{Float64}
    activation::Function

    function SimplicialConv(; in_features::Int, out_features::Int, dimension::Int=0, activation=tanh)
        W_up = randn(out_features, in_features) * sqrt(2.0 / in_features)
        W_down = randn(out_features, in_features) * sqrt(2.0 / in_features)
        W_self = randn(out_features, in_features) * sqrt(2.0 / in_features)
        bias = zeros(out_features)

        new(dimension, in_features, out_features, W_up, W_down, W_self, bias, activation)
    end
end

"""
Forward pass: asymmetric message passing on simplicial complex
"""
function forward_pass(layer::SimplicialConv, complex::SimplicialComplex, features::Matrix{Float64})
    dim = layer.dimension
    n_simplices = size(features, 2)

    # Initialize output
    output = zeros(layer.out_features, n_simplices)

    # Self features
    output .= layer.W_self * features

    # Up messages: from (k-1)-simplices to k-simplices
    if dim > 0
        B_k = boundary_operator(complex, dim)
        # Aggregate from lower-dimensional simplices
        lower_features = complex.features[dim - 1]
        up_messages = B_k' * lower_features'  # Transpose for aggregation
        output .+= layer.W_up * up_messages
    end

    # Down messages: from (k+1)-simplices to k-simplices
    if dim < complex.dimension
        B_kp1 = boundary_operator(complex, dim + 1)
        # Aggregate from higher-dimensional simplices
        higher_features = complex.features[dim + 1]
        down_messages = B_kp1 * higher_features'
        output .+= layer.W_down * down_messages
    end

    # Add bias and activate
    output .+= layer.bias
    output = layer.activation.(output)

    return output
end

"""
Simplicial Pooling: reduce dimension via coarsening
"""
struct SimplicialPooling
    dimension::Int  # Pool from this dimension to lower
    pooling_type::Symbol  # :sum, :mean, :max

    function SimplicialPooling(; dimension::Int, pooling_type::Symbol=:mean)
        new(dimension, pooling_type)
    end
end

function forward_pass(layer::SimplicialPooling, complex::SimplicialComplex, features::Matrix{Float64})
    B_k = boundary_operator(complex, layer.dimension)

    # Pool features from k-simplices to (k-1)-simplices
    if layer.pooling_type == :sum
        pooled = B_k * features'
    elseif layer.pooling_type == :mean
        # Average over incident higher-dimensional simplices
        degrees = vec(sum(abs.(B_k), dims=2))
        pooled = B_k * features'
        pooled = pooled ./ max.(degrees, 1)
    elseif layer.pooling_type == :max
        # Max pooling (requires custom implementation)
        pooled = maximum_pooling(B_k, features)
    else
        error("Unknown pooling type: $(layer.pooling_type)")
    end

    return pooled'
end

function maximum_pooling(boundary::SparseMatrixCSC, features::Matrix{Float64})
    n_lower = size(boundary, 1)
    n_features = size(features, 1)
    pooled = fill(-Inf, n_lower, n_features)

    rows = rowvals(boundary)
    vals = nonzeros(boundary)

    for col in 1:size(boundary, 2)
        for idx in nzrange(boundary, col)
            row = rows[idx]
            # Aggregate max across incident simplices
            pooled[row, :] = max.(pooled[row, :], features[:, col])
        end
    end

    return pooled
end

"""
Full Dir-SNN Model
"""
struct DirSNN
    layers::Vector{Union{SimplicialConv, SimplicialPooling}}

    function DirSNN(layers::Vector)
        new(layers)
    end
end

"""
Forward pass through entire Dir-SNN
"""
function forward_pass(model::DirSNN, complex::SimplicialComplex, initial_features::Dict{Int, Matrix{Float64}})
    # Store features at each dimension
    complex.features = copy(initial_features)

    for layer in model.layers
        dim = layer.dimension
        features = complex.features[dim]

        # Apply layer
        new_features = forward_pass(layer, complex, features)

        # Update features
        if isa(layer, SimplicialConv)
            complex.features[dim] = new_features
        elseif isa(layer, SimplicialPooling)
            complex.features[dim - 1] = new_features
        end
    end

    # Return final features (typically at dimension 0)
    return complex.features[0]
end

"""
E(n)-equivariant message computation (placeholder for full implementation)
"""
function compute_equivariant_messages(positions::Matrix{Float64}, features_in::Matrix{Float64},
                                     edge_indices::Matrix{Int}, W::Matrix{Float64})
    # Compute relative positions (covariant vectors)
    rel_positions = positions[:, edge_indices[2, :]] - positions[:, edge_indices[1, :]]

    # Compute edge features (invariant scalars from distances)
    distances = sqrt.(sum(rel_positions .^ 2, dims=1))

    # Message function combining scalars and vectors
    scalar_messages = W * features_in

    # Modulate by distance-dependent kernel
    # This is a simplified version; full E(n) equivariance requires tensor products

    return scalar_messages
end

end  # module
