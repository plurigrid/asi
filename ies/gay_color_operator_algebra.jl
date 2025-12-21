# ═══════════════════════════════════════════════════════════════════════════════
# GAY.JL COLOR OPERATOR ALGEBRA
# 3-Per-Bifurcation Topology with Entropy Maximization
# ═══════════════════════════════════════════════════════════════════════════════

using Statistics
using LinearAlgebra
using Colors
using Distributions

"""
    ColorOperatorAlgebra

A three-dimensional operator algebra over color space with bifurcating structure.
Each bifurcation point has exactly 3 branches for maximum interaction entropy.
"""
mutable struct ColorOperatorAlgebra
    # Core color data (36 cycles from SplitMix64 generation)
    colors::Vector{RGB{Float64}}
    lch_data::Vector{NamedTuple}

    # Bifurcation structure: 3 branches per node
    # Level 0: root (1 node)
    # Level 1: 3 nodes
    # Level 2: 9 nodes
    # Level 3: 27 nodes
    # etc.
    bifurcation_levels::Int
    bifurcation_tree::Dict{Tuple, Vector{Int}}  # node_path -> color_indices

    # Operator algebra generators (3 per bifurcation)
    generators::Vector{Matrix{Float64}}

    # Entropy metrics
    entropy_per_level::Vector{Float64}
    total_entropy::Float64
end

# Color space constants
const δ_COLOR = 6/29
const κ_COLOR = 841/108
const REF_X = 0.95047
const REF_Y = 1.00000
const REF_Z = 1.08883

"""
    lch_to_rgb(L::Float64, C::Float64, H::Float64)

Convert LCH (Lightness, Chroma, Hue) to RGB via LAB and XYZ.
Uses D65 standard illuminant.
"""
function lch_to_rgb(L::Float64, C::Float64, H::Float64)::RGB{Float64}
    # LCH to LAB
    H_rad = deg2rad(H)
    a = C * cos(H_rad)
    b = C * sin(H_rad)

    # LAB to XYZ (D65)
    fy = (L + 16) / 116
    fx = a / 500 + fy
    fz = fy - b / 200

    # Inverse companding
    xr = if fx > δ_COLOR
        fx^3
    else
        (fx - 16/116) / 7.787
    end
    yr = if L > κ_COLOR * δ_COLOR^2
        fy^3
    else
        L / κ_COLOR
    end
    zr = if fz > δ_COLOR
        fz^3
    else
        (fz - 16/116) / 7.787
    end

    X = xr * REF_X
    Y = yr * REF_Y
    Z = zr * REF_Z

    # XYZ to RGB (sRGB)
    R = X *  3.2406 + Y * -1.5372 + Z * -0.4986
    G = X * -0.9689 + Y *  1.8758 + Z *  0.0415
    B = X *  0.0557 + Y * -0.2040 + Z *  1.0570

    # Apply gamma correction
    gamma_correct = x -> if x <= 0.0031308
        12.92 * x
    else
        1.055 * (x ^ (1/2.4)) - 0.055
    end

    RGB(clamp(gamma_correct(R), 0, 1),
        clamp(gamma_correct(G), 0, 1),
        clamp(gamma_correct(B), 0, 1))
end

"""
    ColorOperatorAlgebra(color_data::Vector, bifurcation_depth::Int=3)

Initialize a color operator algebra from LCH color data with 3-per-bifurcation structure.
"""
function ColorOperatorAlgebra(color_data::Vector, bifurcation_depth::Int=3)
    # Convert LCH to RGB
    colors = [lch_to_rgb(cd[:L], cd[:C], cd[:H]) for cd in color_data]

    # Build bifurcation tree (3-ary tree)
    bifurcation_tree = Dict{Tuple, Vector{Int}}()

    # Recursively build tree
    function build_tree(level::Int, indices::Vector{Int}, path::Tuple)
        if level > bifurcation_depth || isempty(indices)
            return
        end

        # Store leaf colors at this node
        bifurcation_tree[path] = indices

        # Split into 3 groups for next level
        n = length(indices)
        group_size = ceil(Int, n / 3)

        for i in 1:3
            start_idx = (i-1) * group_size + 1
            end_idx = min(i * group_size, n)

            if start_idx <= n
                child_indices = indices[start_idx:end_idx]
                child_path = (path..., i)
                build_tree(level + 1, child_indices, child_path)
            end
        end
    end

    root_path = ()
    build_tree(1, collect(1:length(colors)), root_path)

    # Initialize operators (3 per bifurcation node)
    # Each operator is a 3×3 color space transformation
    generators = []
    for _ in 1:length(bifurcation_tree) * 3
        # Random unitary matrix for color transformation
        push!(generators, qr(randn(3, 3)).Q)
    end

    # Calculate entropy per level
    entropy_per_level = compute_entropy_per_level(colors, bifurcation_tree, bifurcation_depth)
    total_entropy = sum(entropy_per_level)

    ColorOperatorAlgebra(colors, color_data, bifurcation_depth, bifurcation_tree,
                        generators, entropy_per_level, total_entropy)
end

"""
    compute_entropy_per_level(colors::Vector, tree::Dict, max_level::Int)

Compute Shannon entropy of color distribution at each bifurcation level.
"""
function compute_entropy_per_level(colors::Vector{RGB{Float64}},
                                   tree::Dict{Tuple, Vector{Int}},
                                   max_level::Int)::Vector{Float64}
    entropy = Float64[]

    for level in 1:max_level
        level_nodes = [k for k in keys(tree) if length(k) == level]

        if isempty(level_nodes)
            push!(entropy, 0.0)
            continue
        end

        # Color distribution across nodes at this level
        node_sizes = [length(tree[node]) for node in level_nodes]
        probs = node_sizes ./ sum(node_sizes)

        # Shannon entropy: H = -Σ p_i * log2(p_i)
        h = -sum(p * log2(p + 1e-10) for p in probs)
        push!(entropy, h)
    end

    entropy
end

"""
    average_colors_in_operator_algebra(algebra::ColorOperatorAlgebra,
                                       bifurcation_node::Tuple)::RGB{Float64}

Average colors at a bifurcation node using operator algebra weighted averaging.
Maximizes entropy by weighting by chroma (saturation) values.
"""
function average_colors_in_operator_algebra(algebra::ColorOperatorAlgebra,
                                            bifurcation_node::Tuple)::RGB{Float64}
    indices = get(algebra.bifurcation_tree, bifurcation_node, Int[])

    if isempty(indices)
        return RGB(0.5, 0.5, 0.5)  # Default gray
    end

    # Get colors and their chroma values (saturation)
    node_colors = [algebra.colors[i] for i in indices]
    chroma_values = [algebra.lch_data[i][:C] for i in indices]

    # Weight by chroma for maximum entropy (more saturated colors get higher weight)
    weights = chroma_values ./ sum(chroma_values)

    # Weighted average in RGB space
    r = sum(c.r * w for (c, w) in zip(node_colors, weights))
    g = sum(c.g * w for (c, w) in zip(node_colors, weights))
    b = sum(c.b * w for (c, w) in zip(node_colors, weights))

    RGB(clamp(r, 0, 1), clamp(g, 0, 1), clamp(b, 0, 1))
end

"""
    compute_interaction_entropy(algebra::ColorOperatorAlgebra)::Float64

Compute maximum interaction entropy across all bifurcation pathways.
Higher entropy = more diverse color interactions.
"""
function compute_interaction_entropy(algebra::ColorOperatorAlgebra)::Float64
    # Entropy from color distribution across bifurcation tree
    tree_entropy = algebra.total_entropy

    # Entropy from operator generators (linear algebra dimension)
    gen_entropy = 0.0
    for g in algebra.generators[1:min(9, length(algebra.generators))]
        eigs = eigvals(g)
        # Handle complex eigenvalues by taking magnitude
        mag_eigs = abs.(eigs)
        normalized = mag_eigs ./ (sum(mag_eigs) + 1e-10)
        entropy_contribution = -sum(p * log(p + 1e-10) for p in normalized)
        gen_entropy += entropy_contribution
    end

    tree_entropy + gen_entropy / 10  # Normalize generator contribution
end

"""
    apply_operator_to_color_chain(algebra::ColorOperatorAlgebra,
                                  operator_idx::Int)::Vector{RGB{Float64}}

Apply operator transformation to the entire color chain.
"""
function apply_operator_to_color_chain(algebra::ColorOperatorAlgebra,
                                       operator_idx::Int)::Vector{RGB{Float64}}
    if operator_idx > length(algebra.generators)
        return algebra.colors
    end

    operator = algebra.generators[operator_idx]
    transformed = RGB{Float64}[]

    for color in algebra.colors
        # Convert RGB to XYZ for matrix multiplication
        r, g, b = color.r, color.g, color.b
        xyz = [r, g, b]

        # Apply operator
        transformed_xyz = operator * xyz

        # Clamp back to valid RGB range
        push!(transformed, RGB(clamp(transformed_xyz[1], 0, 1),
                              clamp(transformed_xyz[2], 0, 1),
                              clamp(transformed_xyz[3], 0, 1)))
    end

    transformed
end

"""
    print_bifurcation_analysis(algebra::ColorOperatorAlgebra)

Print detailed analysis of bifurcation structure and entropy.
"""
function print_bifurcation_analysis(algebra::ColorOperatorAlgebra)
    println("\n╔════════════════════════════════════════════════════════════════╗")
    println("║     GAY.JL COLOR OPERATOR ALGEBRA - BIFURCATION ANALYSIS    ║")
    println("╚════════════════════════════════════════════════════════════════╝\n")

    println("Structure:")
    println("  Bifurcation depth: $(algebra.bifurcation_levels)")
    println("  Total color cycles: $(length(algebra.colors))")
    println("  Bifurcation nodes: $(length(algebra.bifurcation_tree))")
    println("  Operators (3 per node): $(length(algebra.generators))")

    println("\nEntropy Analysis:")
    for (level, ent) in enumerate(algebra.entropy_per_level)
        println("  Level $level: $(round(ent; digits=4)) bits")
    end
    println("  Total entropy: $(round(algebra.total_entropy; digits=4)) bits")

    interaction_ent = compute_interaction_entropy(algebra)
    println("  Interaction entropy: $(round(interaction_ent; digits=4)) bits")

    println("\nBifurcation Examples:")
    example_nodes = collect(keys(algebra.bifurcation_tree))[1:min(5, length(algebra.bifurcation_tree))]
    for node in example_nodes
        indices = algebra.bifurcation_tree[node]
        avg_color = average_colors_in_operator_algebra(algebra, node)
        println("  Node $node:")
        println("    Colors: $(join(indices, ", "))")
        println("    Average: RGB($(round(avg_color.r; digits=3)), $(round(avg_color.g; digits=3)), $(round(avg_color.b; digits=3)))")
    end

    println("\n✓ Operator algebra ready for codex-rs integration")
end

export ColorOperatorAlgebra, lch_to_rgb, average_colors_in_operator_algebra,
       compute_interaction_entropy, apply_operator_to_color_chain,
       print_bifurcation_analysis
