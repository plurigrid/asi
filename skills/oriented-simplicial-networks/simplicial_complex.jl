"""
Simplicial Complex Construction and Operators

Implements oriented simplicial complexes with boundary operators,
Laplacians, and E(n)-equivariant feature initialization.
"""

module SimplicialComplexModule

export SimplicialComplex, boundary_operator, laplacian, hodge_laplacian
export oriented_incidence_matrix, add_simplex!, compute_persistent_homology

using LinearAlgebra
using SparseArrays

"""
Oriented Simplex: vertices ordered with orientation sign
"""
struct OrientedSimplex
    vertices::Vector{Int}
    dimension::Int
    orientation::Int  # +1 or -1
    features::Union{Nothing, Vector{Float64}}
end

"""
Simplicial Complex with orientation tracking
"""
mutable struct SimplicialComplex
    dimension::Int
    simplices::Vector{Vector{OrientedSimplex}}  # simplices[k+1] = k-simplices
    boundaries::Vector{SparseMatrixCSC{Int, Int}}  # boundary operators
    features::Dict{Int, Matrix{Float64}}  # features per dimension

    function SimplicialComplex(max_dim::Int)
        new(max_dim,
            [OrientedSimplex[] for _ in 1:(max_dim+1)],
            SparseMatrixCSC{Int, Int}[],
            Dict{Int, Matrix{Float64}}())
    end
end

"""
Add oriented simplex to complex
"""
function add_simplex!(complex::SimplicialComplex, vertices::Vector{Int}, features=nothing)
    dim = length(vertices) - 1
    @assert dim <= complex.dimension "Simplex dimension exceeds complex dimension"

    # Canonicalize orientation: sort vertices, track sign
    sorted_vertices, orientation = canonicalize_orientation(vertices)

    simplex = OrientedSimplex(sorted_vertices, dim, orientation, features)
    push!(complex.simplices[dim + 1], simplex)

    return simplex
end

"""
Canonicalize simplex orientation via sorting
"""
function canonicalize_orientation(vertices::Vector{Int})
    perm = sortperm(vertices)
    sorted = vertices[perm]
    # Orientation is sign of permutation
    orientation = parity(perm)
    return sorted, orientation
end

function parity(perm::Vector{Int})
    # Count inversions to determine permutation sign
    n = length(perm)
    inversions = 0
    for i in 1:n
        for j in (i+1):n
            if perm[i] > perm[j]
                inversions += 1
            end
        end
    end
    return iseven(inversions) ? 1 : -1
end

"""
Compute boundary operator ∂_k: C_k → C_{k-1}
"""
function boundary_operator(complex::SimplicialComplex, k::Int)
    @assert 0 < k <= complex.dimension "Invalid dimension for boundary operator"

    k_simplices = complex.simplices[k + 1]
    km1_simplices = complex.simplices[k]

    n_k = length(k_simplices)
    n_km1 = length(km1_simplices)

    I = Int[]
    J = Int[]
    V = Int[]

    for (j, sigma) in enumerate(k_simplices)
        # For each face of sigma
        for i in 0:k
            # Remove i-th vertex to get face
            face_vertices = [sigma.vertices[l] for l in 1:(k+1) if l != i+1]
            face_idx = find_simplex_index(km1_simplices, face_vertices)

            if face_idx !== nothing
                # Coefficient is (-1)^i times orientation
                coeff = ((-1)^i) * sigma.orientation
                push!(I, face_idx)
                push!(J, j)
                push!(V, coeff)
            end
        end
    end

    return sparse(I, J, V, n_km1, n_k)
end

"""
Find simplex index in list by vertices
"""
function find_simplex_index(simplices::Vector{OrientedSimplex}, vertices::Vector{Int})
    sorted_vertices, _ = canonicalize_orientation(vertices)
    for (idx, s) in enumerate(simplices)
        if s.vertices == sorted_vertices
            return idx
        end
    end
    return nothing
end

"""
Compute k-th Hodge Laplacian: L_k = ∂_{k+1} ∂_{k+1}^T + ∂_k^T ∂_k
"""
function hodge_laplacian(complex::SimplicialComplex, k::Int)
    B_k = k > 0 ? boundary_operator(complex, k) : spzeros(0, length(complex.simplices[1]))
    B_kp1 = k < complex.dimension ? boundary_operator(complex, k+1) : spzeros(length(complex.simplices[k+1]), 0)

    L_down = B_k' * B_k
    L_up = B_kp1 * B_kp1'

    return L_down + L_up
end

"""
Simplified Laplacian for dimension k
"""
function laplacian(complex::SimplicialComplex, k::Int)
    return hodge_laplacian(complex, k)
end

"""
Compute persistent homology (stub - integrates with external library)
"""
function compute_persistent_homology(complex::SimplicialComplex; max_dim::Int=2)
    # TODO: Integration with Ripser.jl or custom persistence computation
    # Returns persistence diagrams for each dimension

    diagrams = Dict{Int, Matrix{Float64}}()

    for dim in 0:min(max_dim, complex.dimension)
        # Placeholder: would compute birth/death pairs
        diagrams[dim] = zeros(0, 2)  # Empty diagram
    end

    return diagrams
end

"""
Initialize E(n)-equivariant features on vertices
"""
function init_equivariant_features(positions::Matrix{Float64}, feature_dim::Int)
    n_vertices = size(positions, 2)

    # Type-0 features: scalars (invariant)
    scalar_features = randn(feature_dim ÷ 3, n_vertices)

    # Type-1 features: vectors (covariant)
    vector_features = randn(3, feature_dim ÷ 3, n_vertices)

    # Type-2 features: higher-order tensors
    # For simplicity, use scalar + vector representation

    return Dict(
        :scalar => scalar_features,
        :vector => vector_features
    )
end

end  # module
