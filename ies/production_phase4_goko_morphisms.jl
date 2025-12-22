# Phase 4: Compute GOKO Morphisms
# File: production_phase4_goko_morphisms.jl

using LinearAlgebra
using Statistics
using Base64

println("\n" * "="^80)
println("PHASE 4: GOKO MORPHISM COMPUTATION")
println("="^80)

# ============================================================================
# Step 1: Load GMRA from Phase 1
# ============================================================================

println("\n[Step 1: Loading GMRA]")

if !@isdefined(gmra)
    println("  Loading GMRA from GMRA_WORLDS_UNWORLDING.jl...")
    include("GMRA_WORLDS_UNWORLDING.jl")
end

println("  ✓ GMRA loaded ($(length(gmra.skills)) skills)")

# ============================================================================
# Step 2: Load Embeddings from Phase 3
# ============================================================================

function load_embeddings_json(json_path::String)::Dict{Int, Vector{Float64}}
    """Load base64-encoded embeddings from JSON file."""

    # Parse JSON manually (no external dependency)
    json_text = read(json_path, String)

    # Extract embeddings section
    embed_start = findfirst("\"embeddings\":", json_text)
    if isnothing(embed_start)
        error("Could not find embeddings in JSON")
    end

    embeddings = Dict{Int, Vector{Float64}}()

    # Split by skill entries (simple heuristic)
    lines = split(json_text, '\n')

    for line in lines
        if contains(line, ": \"")
            # Try to extract skill ID and embedding
            try
                # Format: "123": "base64data",
                parts = split(strip(line, [' ', ',', '"']), "\": \"")
                if length(parts) >= 2
                    skill_id_str = parts[1]
                    embedding_b64 = parts[2]

                    skill_id = tryparse(Int, skill_id_str)
                    if !isnothing(skill_id) && length(embedding_b64) > 10
                        # Decode base64
                        try
                            embedding_bytes = base64decode(embedding_b64)

                            # Convert bytes to Float64 vector (384 elements, 4 bytes each)
                            n_floats = div(length(embedding_bytes), 4)
                            embedding = reinterpret(Float32, embedding_bytes) |> Vector
                            embeddings[skill_id] = Float64.(embedding)
                        catch
                            # Skip if decoding fails
                        end
                    end
                end
            catch
                # Skip malformed lines
            end
        end
    end

    if isempty(embeddings)
        error("Failed to parse any embeddings from $json_path")
    end

    return embeddings
end

println("\n[Step 2: Loading Embeddings]")

embeddings_dict = load_embeddings_json("skill_embeddings_lightweight.json")
println("  ✓ Loaded $(length(embeddings_dict)) embeddings")

# Check dimension
sample_embedding = embeddings_dict[1]
println("  ✓ Embedding dimension: $(length(sample_embedding))")

# Update GMRA skills with real embeddings
for skill in gmra.skills
    if haskey(embeddings_dict, skill.id)
        skill.semantic_embedding = embeddings_dict[skill.id]
    else
        println("  ⚠ Warning: No embedding for skill $(skill.id)")
    end
end

println("  ✓ Updated GMRA skills with real embeddings")

# ============================================================================
# Step 3: Compute k-NN Graph
# ============================================================================

function compute_knn_graph(embeddings::Dict{Int, Vector{Float64}}, k::Int=5)::Vector{Tuple{Int, Int, Float64}}
    """
    Compute k-NN graph with Euclidean distances.

    Returns:
        Vector of (source, target, distance) tuples
    """

    println("\n[Step 3: Computing k-NN Graph]")
    println("  k=$k neighbors per skill")

    skill_ids = sort(collect(keys(embeddings)))
    n_skills = length(skill_ids)
    edges = Tuple{Int, Int, Float64}[]

    println("  Computing distances...")

    for (idx_i, i) in enumerate(skill_ids)
        emb_i = embeddings[i]

        # Compute distances to all other skills
        distances = Float64[]
        j_indices = Int[]

        for (idx_j, j) in enumerate(skill_ids)
            if i != j
                dist = norm(emb_i - embeddings[j])
                push!(distances, dist)
                push!(j_indices, j)
            end
        end

        # Find k nearest neighbors
        if !isempty(distances)
            sorted_idx = sortperm(distances)[1:min(k, length(distances))]

            for neighbor_rank in sorted_idx
                j = j_indices[neighbor_rank]
                distance = distances[neighbor_rank]
                push!(edges, (i, j, distance))
            end
        end

        # Progress
        if idx_i % 50 == 0 || idx_i == n_skills
            percent = Int(round(100 * idx_i / n_skills))
            print("  [$percent%] ")
        end
    end

    println("\n  ✓ Computed $(length(edges)) edges")

    return edges
end

knn_edges = compute_knn_graph(embeddings_dict, 5)

# ============================================================================
# Step 4: Compute GOKO Morphisms
# ============================================================================

function edges_to_morphisms(edges::Vector{Tuple{Int, Int, Float64}})::Vector{Dict}
    """
    Convert k-NN edges to GOKO morphisms.
    Morphism includes Wasserstein distance and optimal transport cost.
    """

    println("\n[Step 4: Computing GOKO Morphisms]")

    morphisms = Dict[]

    for (source, target, wasserstein_dist) in edges
        # Optimal transport cost (Wasserstein)
        ot_cost = wasserstein_dist^2 / 2

        push!(morphisms, Dict(
            "source" => source,
            "target" => target,
            "wasserstein_distance" => wasserstein_dist,
            "optimal_transport_cost" => ot_cost
        ))
    end

    println("  ✓ Created $(length(morphisms)) morphisms")

    return morphisms
end

morphisms = edges_to_morphisms(knn_edges)

# ============================================================================
# Step 5: Analyze Morphism Network
# ============================================================================

function analyze_morphisms(morphisms::Vector{Dict})
    """Compute statistics on morphism network."""

    println("\n[Step 5: Analyzing Morphism Network]")

    distances = [m["wasserstein_distance"] for m in morphisms]
    costs = [m["optimal_transport_cost"] for m in morphisms]

    println("\n  Distance Statistics:")
    println("    Mean: $(round(mean(distances), digits=4))")
    println("    Median: $(round(median(distances), digits=4))")
    println("    Std: $(round(std(distances), digits=4))")
    println("    Min: $(round(minimum(distances), digits=4))")
    println("    Max: $(round(maximum(distances), digits=4))")

    println("\n  Cost Statistics:")
    println("    Mean: $(round(mean(costs), digits=4))")
    println("    Total: $(round(sum(costs), digits=2))")

    # Distance distribution
    short_range = sum(1 for d in distances if d < 0.3)
    medium_range = sum(1 for d in distances if (0.3 <= d < 0.6))
    long_range = sum(1 for d in distances if d >= 0.6)

    println("\n  Distance Distribution:")
    println("    Short (<0.3): $short_range ($(round(100*short_range/length(distances), digits=1))%)")
    println("    Medium (0.3-0.6): $medium_range ($(round(100*medium_range/length(distances), digits=1))%)")
    println("    Long (≥0.6): $long_range ($(round(100*long_range/length(distances), digits=1))%)")

    println("\n  Network Properties:")
    n_unique_sources = length(unique([m["source"] for m in morphisms]))
    n_unique_targets = length(unique([m["target"] for m in morphisms]))
    n_skills = max(n_unique_sources, n_unique_targets)
    density = length(morphisms) / (n_skills * (n_skills - 1) / 2)

    println("    Unique sources: $n_unique_sources")
    println("    Unique targets: $n_unique_targets")
    println("    Network density: $(round(100*density, digits=2))%")
    println("    Avg edges per node: $(round(length(morphisms) / n_skills, digits=1))")
end

analyze_morphisms(morphisms)

# ============================================================================
# Step 6: Save Morphisms
# ============================================================================

function save_morphisms_tsv(morphisms::Vector{Dict}, output_path::String)
    """Save morphisms to TSV file."""

    println("\n[Step 6: Saving Morphisms]")

    open(output_path, "w") do f
        write(f, "source\ttarget\twasserstein_distance\toptimal_transport_cost\n")

        for morph in morphisms
            write(f, "$(morph["source"])\t$(morph["target"])\t$(morph["wasserstein_distance"])\t$(morph["optimal_transport_cost"])\n")
        end
    end

    println("  ✓ Saved $(length(morphisms)) morphisms to $output_path")
end

save_morphisms_tsv(morphisms, "goko_morphisms.tsv")

# ============================================================================
# SUMMARY
# ============================================================================

println("\n" * "="^80)
println("PHASE 4 COMPLETE: GOKO Morphisms Computed")
println("="^80)

println("\n✓ Summary:")
println("  GMRA Skills: $(length(gmra.skills))")
println("  Embeddings loaded: $(length(embeddings_dict))")
println("  Embedding dimension: $(length(embeddings_dict[1]))")
println("  k-NN edges computed: $(length(morphisms))")
println("  Morphisms saved to: goko_morphisms.tsv")

println("\n✓ Ready for Phase 5-6: IsUMAP Projection & Visualization")
println("  Next: python3 production_phase5_isumap_projection.py")
