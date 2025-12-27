"""
Sheaf Laplacian and Consensus Dynamics

Implements weighted Laplacian on cellular sheaves for consensus,
diffusion, and spectral analysis.
"""

module SheafLaplacianModule

export sheaf_laplacian, sheaf_diffusion, spectral_gap
export consensus_dynamics, laplacian_eigendecomposition

using LinearAlgebra
using SparseArrays
include("cellular_sheaf.jl")
using .CellularSheafModule

"""
Compute sheaf Laplacian L = δ^0* δ^0 + δ^1 δ^1*

For dimension 0 (vertex cochains):
L_0 = (δ^0)^T δ^0
"""
function sheaf_laplacian(sheaf::CellularSheaf, dimension::Int=0)
    if dimension == 0
        δ0 = compute_coboundary(sheaf, 0)
        return δ0' * δ0
    elseif dimension == 1
        δ0 = compute_coboundary(sheaf, 0)
        δ1 = compute_coboundary(sheaf, 1)
        return δ0' * δ0 + δ1 * δ1'
    else
        error("Laplacian for dimension > 1 not implemented")
    end
end

"""
Sheaf diffusion: evolve x(t+1) = (I - α L) x(t)
"""
function sheaf_diffusion(sheaf::CellularSheaf, initial::Vector{Float64};
                         steps::Int=100, step_size::Float64=0.01)
    L = sheaf_laplacian(sheaf, 0)
    n = size(L, 1)

    # Diffusion operator
    diffusion_op = I - step_size * L

    # Iterate
    x = copy(initial)
    trajectory = [x]

    for _ in 1:steps
        x = diffusion_op * x
        push!(trajectory, copy(x))
    end

    return trajectory
end

"""
Consensus dynamics with partial observations
"""
function consensus_dynamics(sheaf::CellularSheaf,
                           observed_nodes::Vector{Int},
                           observations::Vector{Vector{Float64}};
                           max_iter::Int=1000,
                           tolerance::Float64=1e-6)
    L = sheaf_laplacian(sheaf, 0)
    n_nodes = length(sheaf.stalks)
    d = sheaf.stalk_dim
    n = n_nodes * d

    # Initialize with observations
    x = zeros(n)
    for (i, node) in enumerate(observed_nodes)
        x[(node-1)*d+1 : node*d] = observations[i]
    end

    # Gradient descent on ||Lx||^2 + λ ||x - observations||^2
    λ = 1.0

    for iter in 1:max_iter
        # Gradient of energy function
        grad = L' * L * x

        # Add observation constraint
        for (i, node) in enumerate(observed_nodes)
            idx_range = (node-1)*d+1 : node*d
            grad[idx_range] += λ * (x[idx_range] - observations[i])
        end

        # Update
        step_size = 0.01
        x_new = x - step_size * grad

        # Check convergence
        if norm(x_new - x) < tolerance
            break
        end

        x = x_new
    end

    return x
end

"""
Compute spectral gap of sheaf Laplacian
"""
function spectral_gap(sheaf::CellularSheaf)
    L = Matrix(sheaf_laplacian(sheaf, 0))

    # Compute eigenvalues
    eigenvals = eigvals(Symmetric(L))
    sort!(eigenvals)

    # Spectral gap is difference between first nonzero eigenvalue and zero
    # (assumes connected complex with trivial H^0)

    # Find first significantly nonzero eigenvalue
    tol = 1e-8
    nonzero_eigs = eigenvals[eigenvals .> tol]

    if length(nonzero_eigs) >= 1
        return nonzero_eigs[1]
    else
        return 0.0
    end
end

"""
Full eigendecomposition of sheaf Laplacian
"""
function laplacian_eigendecomposition(sheaf::CellularSheaf)
    L = Matrix(sheaf_laplacian(sheaf, 0))

    # Symmetric eigendecomposition
    eigen_result = eigen(Symmetric(L))

    return (
        eigenvalues = eigen_result.values,
        eigenvectors = eigen_result.vectors
    )
end

"""
Effective resistance between two nodes in sheaf
"""
function effective_resistance(sheaf::CellularSheaf, node_i::Int, node_j::Int)
    d = sheaf.stalk_dim
    L = Matrix(sheaf_laplacian(sheaf, 0))

    # Pseudoinverse of Laplacian
    L_pinv = pinv(L)

    # Resistance = (e_i - e_j)^T L^+ (e_i - e_j)
    e_diff = zeros(size(L, 1))
    e_diff[(node_i-1)*d+1 : node_i*d] .= 1.0
    e_diff[(node_j-1)*d+1 : node_j*d] .- = 1.0

    resistance = e_diff' * L_pinv * e_diff

    return resistance
end

end  # module
