#!/usr/bin/env julia

"""
Bidirectional Behavioral Awareness: Skill Neighborhood Introspection

SUBTEXT (Interpolation):
Each skill is aware of:
- Its own representations (.org, tangled, geodesic)
- Its behavioral neighbors (skills with similar trits/behaviors)
- Its citation neighbors (skills it references/referenced by)

SUPERSTRUCTURE (Extrapolation):
The network of skills forms a mutually recursive awareness graph where:
- Each node = (skill, representations, awareness)
- Each edge = (behavioral similarity, citation, morphism)
- Introspection = skill queries its own neighborhood
- Extrapolation = skill predicts未observed connections

This creates a SELF-AWARE skill system.
"""

using JSON
using Printf

# ============================================================================
# Data Structures
# ============================================================================

struct Representation
    type::Symbol  # :org, :tangled, :geodesic
    path::String
    exists::Bool
    line_count::Int
    size_bytes::Int
end

struct BehavioralSignature
    has_code::Bool
    primary_language::String
    code_block_count::Int
    trit::Union{Int, Nothing}
    execution_path_length::Int  # 1 for geodesic, 2 for tangled
end

mutable struct SkillNode
    name::String
    skill_dir::String
    representations::Vector{Representation}
    behavior::BehavioralSignature
    cited_by::Vector{String}
    cites::Vector{String}
    trit_neighbors::Vector{String}  # Skills with same trit
    behavior_neighbors::Vector{String}  # Skills with similar behavior
end

struct BidirectionalEdge
    from::String
    to::String
    edge_type::Symbol  # :citation, :trit_equivalence, :behavioral_similarity
    weight::Float64
end

struct AwarenessGraph
    nodes::Dict{String, SkillNode}
    edges::Vector{BidirectionalEdge}
end

# ============================================================================
# Representation Detection
# ============================================================================

function detect_representations(skill_dir::String)::Vector{Representation}
    reps = Representation[]
    
    # Look for .org files
    for file in readdir(skill_dir, join=true)
        if endswith(file, ".org")
            stats = stat(file)
            push!(reps, Representation(
                :org,
                file,
                true,
                length(readlines(file)),
                stats.size
            ))
        end
    end
    
    # Look for geodesics
    geodesic_dir = joinpath(skill_dir, "geodesics")
    if isdir(geodesic_dir)
        for file in readdir(geodesic_dir, join=true)
            if occursin(r"\.geodesic\.", basename(file))
                stats = stat(file)
                push!(reps, Representation(
                    :geodesic,
                    file,
                    true,
                    length(readlines(file)),
                    stats.size
                ))
            end
        end
    end
    
    # Look for tangled source files (heuristic: .jl, .py, .clj not in geodesics/)
    for ext in [".jl", ".py", ".clj", ".scm"]
        for file in readdir(skill_dir, join=true)
            if endswith(file, ext) && !occursin("geodesics", file)
                stats = stat(file)
                push!(reps, Representation(
                    :tangled,
                    file,
                    true,
                    length(readlines(file)),
                    stats.size
                ))
            end
        end
    end
    
    return reps
end

function infer_behavior(reps::Vector{Representation}, skill_name::String, trit_map::Dict)::BehavioralSignature
    has_code = any(r.type in [:org, :geodesic, :tangled] for r in reps)
    
    # Detect primary language
    lang_counts = Dict{String, Int}()
    for rep in reps
        if rep.type == :geodesic
            if endswith(rep.path, ".jl")
                lang_counts["julia"] = get(lang_counts, "julia", 0) + 1
            elseif endswith(rep.path, ".py")
                lang_counts["python"] = get(lang_counts, "python", 0) + 1
            elseif endswith(rep.path, ".clj")
                lang_counts["clojure"] = get(lang_counts, "clojure", 0) + 1
            end
        end
    end
    
    primary_lang = if !isempty(lang_counts)
        first(sort(collect(lang_counts), by=x->x[2], rev=true))[1]
    else
        "none"
    end
    
    code_block_count = count(r.type == :org for r in reps)
    
    trit = get(trit_map, skill_name, nothing)
    
    # Execution path length: 1 if geodesic exists, 2 if only tangled
    has_geodesic = any(r.type == :geodesic for r in reps)
    exec_path_length = has_geodesic ? 1 : 2
    
    return BehavioralSignature(
        has_code,
        primary_lang,
        code_block_count,
        trit,
        exec_path_length
    )
end

# ============================================================================
# Citation Graph Extraction
# ============================================================================

function extract_citations(skill_dir::String)::Tuple{Vector{String}, Vector{String}}
    """
    Parse SKILL.md for Related Skills section.
    Returns (cites, cited_by) - for now we compute cited_by in second pass.
    """
    cites = String[]
    
    skill_md = joinpath(skill_dir, "SKILL.md")
    if !isfile(skill_md)
        return (cites, String[])
    end
    
    in_related = false
    for line in eachline(skill_md)
        if occursin(r"^##\s+Related Skills", line)
            in_related = true
            continue
        elseif startswith(line, "##") && in_related
            break
        end
        
        if in_related && occursin(r"`([a-z0-9\-]+)`", line)
            for m in eachmatch(r"`([a-z0-9\-]+)`", line)
                cited = m.captures[1]
                push!(cites, cited)
            end
        end
    end
    
    return (unique(cites), String[])
end

# ============================================================================
# Trit Loading
# ============================================================================

function load_trit_assignments(asi_root::String)::Dict{String, Int}
    trit_file = joinpath(asi_root, "skills", "coequalizers", "skill_trit_assignments.json")
    
    if !isfile(trit_file)
        return Dict{String, Int}()
    end
    
    data = JSON.parsefile(trit_file)
    
    trit_map = Dict{String, Int}()
    for (trit_str, skills) in data
        trit_val = parse(Int, trit_str)
        for skill in skills
            trit_map[skill] = trit_val
        end
    end
    
    return trit_map
end

# ============================================================================
# Neighborhood Construction
# ============================================================================

function find_trit_neighbors(skill::String, trit::Union{Int, Nothing}, all_trits::Dict{String, Int})::Vector{String}
    if trit === nothing
        return String[]
    end
    
    neighbors = String[]
    for (other, other_trit) in all_trits
        if other != skill && other_trit == trit
            push!(neighbors, other)
        end
    end
    
    return neighbors
end

function find_behavioral_neighbors(
    skill::SkillNode, 
    all_nodes::Dict{String, SkillNode},
    threshold::Float64=0.5
)::Vector{String}
    """
    Behavioral similarity based on:
    - Same primary language
    - Similar code block count
    - Same execution path length
    """
    
    neighbors = String[]
    
    for (other_name, other) in all_nodes
        if other_name == skill.name
            continue
        end
        
        similarity = 0.0
        
        # Language match
        if skill.behavior.primary_language == other.behavior.primary_language && 
           skill.behavior.primary_language != "none"
            similarity += 0.4
        end
        
        # Code block count similarity
        if skill.behavior.code_block_count > 0 && other.behavior.code_block_count > 0
            ratio = min(skill.behavior.code_block_count, other.behavior.code_block_count) / 
                    max(skill.behavior.code_block_count, other.behavior.code_block_count)
            similarity += 0.3 * ratio
        end
        
        # Execution path length (geodesic vs tangled)
        if skill.behavior.execution_path_length == other.behavior.execution_path_length
            similarity += 0.3
        end
        
        if similarity >= threshold
            push!(neighbors, other_name)
        end
    end
    
    return neighbors
end

# ============================================================================
# Graph Construction
# ============================================================================

function build_awareness_graph(asi_root::String)::AwarenessGraph
    skills_dir = joinpath(asi_root, "skills")
    trit_map = load_trit_assignments(asi_root)
    
    # First pass: create nodes
    nodes = Dict{String, SkillNode}()
    
    for entry in readdir(skills_dir)
        skill_path = joinpath(skills_dir, entry)
        if !isdir(skill_path) || startswith(entry, ".")
            continue
        end
        
        skill_name = entry
        reps = detect_representations(skill_path)
        behavior = infer_behavior(reps, skill_name, trit_map)
        (cites, _) = extract_citations(skill_path)
        
        trit = get(trit_map, skill_name, nothing)
        trit_neighbors = find_trit_neighbors(skill_name, trit, trit_map)
        
        node = SkillNode(
            skill_name,
            skill_path,
            reps,
            behavior,
            String[],  # Will fill in second pass
            cites,
            trit_neighbors,
            String[]  # Will fill after all nodes created
        )
        
        nodes[skill_name] = node
    end
    
    # Second pass: compute cited_by and behavioral neighbors
    for (name, node) in nodes
        # Reverse citations
        for cited in node.cites
            if haskey(nodes, cited)
                push!(nodes[cited].cited_by, name)
            end
        end
        
        # Behavioral neighbors
        node.behavior_neighbors = find_behavioral_neighbors(node, nodes)
    end
    
    # Third pass: create edges
    edges = BidirectionalEdge[]
    
    for (name, node) in nodes
        # Citation edges
        for cited in node.cites
            if haskey(nodes, cited)
                push!(edges, BidirectionalEdge(name, cited, :citation, 1.0))
            end
        end
        
        # Trit equivalence edges
        for neighbor in node.trit_neighbors
            if haskey(nodes, neighbor)
                # Only add edge once (from lower to higher name alphabetically)
                if name < neighbor
                    push!(edges, BidirectionalEdge(name, neighbor, :trit_equivalence, 1.0))
                end
            end
        end
        
        # Behavioral similarity edges
        for neighbor in node.behavior_neighbors
            if haskey(nodes, neighbor)
                if name < neighbor
                    push!(edges, BidirectionalEdge(name, neighbor, :behavioral_similarity, 0.5))
                end
            end
        end
    end
    
    return AwarenessGraph(nodes, edges)
end

# ============================================================================
# Introspection: Skill Self-Awareness
# ============================================================================

function introspect(graph::AwarenessGraph, skill_name::String)
    """
    A skill examines its own representations and neighborhood.
    """
    
    if !haskey(graph.nodes, skill_name)
        println("⚠ Skill not found: $skill_name")
        return
    end
    
    node = graph.nodes[skill_name]
    
    println("=" ^ 70)
    println("INTROSPECTION: $skill_name")
    println("=" ^ 70)
    println()
    
    # Self-awareness: representations
    println("📄 My Representations:")
    for rep in node.representations
        type_icon = rep.type == :org ? "📖" : rep.type == :geodesic ? "🎯" : "📝"
        println("  $type_icon $(rep.type): $(basename(rep.path))")
        println("     Lines: $(rep.line_count), Size: $(rep.size_bytes) bytes")
    end
    println()
    
    # Behavioral signature
    println("🧬 My Behavior:")
    println("  Has code: $(node.behavior.has_code)")
    println("  Primary language: $(node.behavior.primary_language)")
    println("  Code blocks: $(node.behavior.code_block_count)")
    println("  Trit: $(node.behavior.trit === nothing ? "unknown" : node.behavior.trit)")
    println("  Execution path: $(node.behavior.execution_path_length == 1 ? "geodesic (1-step)" : "tangled (2-step)")")
    println()
    
    # Citation awareness
    println("🔗 My Citations:")
    if !isempty(node.cites)
        println("  I cite: $(join(node.cites, ", "))")
    else
        println("  I cite: (none)")
    end
    
    if !isempty(node.cited_by)
        println("  Cited by: $(join(node.cited_by, ", "))")
    else
        println("  Cited by: (none)")
    end
    println()
    
    # Neighborhood awareness
    println("👥 My Neighborhood:")
    if !isempty(node.trit_neighbors)
        println("  Trit neighbors ($(length(node.trit_neighbors))): $(join(node.trit_neighbors[1:min(5, end)], ", "))$(length(node.trit_neighbors) > 5 ? "..." : "")")
    end
    
    if !isempty(node.behavior_neighbors)
        println("  Behavioral neighbors ($(length(node.behavior_neighbors))): $(join(node.behavior_neighbors[1:min(5, end)], ", "))$(length(node.behavior_neighbors) > 5 ? "..." : "")")
    end
    println()
end

# ============================================================================
# Extrapolation: Predict Unobserved Connections
# ============================================================================

function extrapolate(graph::AwarenessGraph, skill_name::String)
    """
    Given a skill's neighborhood, predict未observed but likely connections.
    
    Uses transitive closure and similarity propagation.
    """
    
    if !haskey(graph.nodes, skill_name)
        println("⚠ Skill not found: $skill_name")
        return
    end
    
    node = graph.nodes[skill_name]
    
    println("=" ^ 70)
    println("EXTRAPOLATION: $skill_name")
    println("=" ^ 70)
    println()
    
    # Transitive citation candidates
    println("🔮 Predicted Citation Candidates:")
    citation_candidates = Set{String}()
    
    for cited in node.cites
        if haskey(graph.nodes, cited)
            cited_node = graph.nodes[cited]
            for transitive in cited_node.cites
                if transitive != skill_name && !(transitive in node.cites)
                    push!(citation_candidates, transitive)
                end
            end
        end
    end
    
    if !isempty(citation_candidates)
        for candidate in collect(citation_candidates)[1:min(5, end)]
            println("  → $candidate (transitive through citations)")
        end
    else
        println("  (none predicted)")
    end
    println()
    
    # Behavioral similarity propagation
    println("🧠 Predicted Behavioral Neighbors:")
    behavior_candidates = Set{String}()
    
    for neighbor in node.behavior_neighbors
        if haskey(graph.nodes, neighbor)
            neighbor_node = graph.nodes[neighbor]
            for second_order in neighbor_node.behavior_neighbors
                if second_order != skill_name && !(second_order in node.behavior_neighbors)
                    push!(behavior_candidates, second_order)
                end
            end
        end
    end
    
    if !isempty(behavior_candidates)
        for candidate in collect(behavior_candidates)[1:min(5, end)]
            println("  → $candidate (similar to my neighbors)")
        end
    else
        println("  (none predicted)")
    end
    println()
    
    # Trit-based morphisms
    if node.behavior.trit !== nothing
        println("⚕️ Potential GF(3) Triad Partners:")
        trit = node.behavior.trit
        needed_sum = (3 - (trit % 3)) % 3  # What's needed to balance to 0 (mod 3)
        
        partners = String[]
        for (other_name, other_node) in graph.nodes
            if other_name != skill_name && other_node.behavior.trit !== nothing
                if (trit + other_node.behavior.trit) % 3 == 0
                    push!(partners, other_name)
                end
            end
        end
        
        if !isempty(partners)
            for partner in partners[1:min(5, end)]
                partner_trit = graph.nodes[partner].behavior.trit
                println("  → $partner (trit=$partner_trit, forms balanced pair)")
            end
        else
            println("  (no direct pairs found)")
        end
    end
    println()
end

# ============================================================================
# Mutually Recursive Awareness: All Skills Introspect Simultaneously
# ============================================================================

function mutual_introspection(graph::AwarenessGraph, focus_skills::Vector{String})
    """
    Multiple skills introspect each other simultaneously.
    Creates awareness of mutual awareness.
    """
    
    println("=" ^ 70)
    println("MUTUAL INTROSPECTION")
    println("=" ^ 70)
    println()
    
    for skill in focus_skills
        if haskey(graph.nodes, skill)
            node = graph.nodes[skill]
            
            # What does this skill know about the others?
            println("$skill is aware of:")
            for other in focus_skills
                if other == skill
                    continue
                end
                
                # Check all connection types
                connections = String[]
                
                if other in node.cites
                    push!(connections, "cites")
                end
                if other in node.cited_by
                    push!(connections, "cited-by")
                end
                if other in node.trit_neighbors
                    push!(connections, "trit-neighbor")
                end
                if other in node.behavior_neighbors
                    push!(connections, "behavior-neighbor")
                end
                
                if !isempty(connections)
                    println("  → $other: $(join(connections, ", "))")
                end
            end
            println()
        end
    end
end

# ============================================================================
# Main
# ============================================================================

function main()
    asi_root = dirname(dirname(@__DIR__))
    
    println("Building bidirectional awareness graph...")
    graph = build_awareness_graph(asi_root)
    
    println("✓ Graph built:")
    println("  Nodes (skills): $(length(graph.nodes))")
    println("  Edges: $(length(graph.edges))")
    println()
    
    # Introspection examples
    example_skills = ["coequalizers", "org-babel-execution", "bisimulation-game", "oapply-colimit"]
    
    for skill in example_skills
        if haskey(graph.nodes, skill)
            introspect(graph, skill)
            extrapolate(graph, skill)
        end
    end
    
    # Mutual awareness
    println("\n")
    mutual_introspection(graph, example_skills)
    
    # Summary statistics
    println("=" ^ 70)
    println("GRAPH STATISTICS")
    println("=" ^ 70)
    println()
    
    # Count representation types
    org_count = sum(any(r.type == :org for r in node.representations) for node in values(graph.nodes))
    geodesic_count = sum(any(r.type == :geodesic for r in node.representations) for node in values(graph.nodes))
    tangled_count = sum(any(r.type == :tangled for r in node.representations) for node in values(graph.nodes))
    
    println("Representation coverage:")
    println("  Skills with .org files: $org_count")
    println("  Skills with geodesics: $geodesic_count")
    println("  Skills with tangled sources: $tangled_count")
    println()
    
    # Edge type distribution
    citation_edges = count(e.edge_type == :citation for e in graph.edges)
    trit_edges = count(e.edge_type == :trit_equivalence for e in graph.edges)
    behavior_edges = count(e.edge_type == :behavioral_similarity for e in graph.edges)
    
    println("Edge type distribution:")
    println("  Citation: $citation_edges")
    println("  Trit equivalence: $trit_edges")
    println("  Behavioral similarity: $behavior_edges")
    println()
    
    # Most connected skills
    connectivity = Dict{String, Int}()
    for edge in graph.edges
        connectivity[edge.from] = get(connectivity, edge.from, 0) + 1
        connectivity[edge.to] = get(connectivity, edge.to, 0) + 1
    end
    
    top_connected = sort(collect(connectivity), by=x->x[2], rev=true)[1:min(10, end)]
    
    println("Most connected skills:")
    for (skill, count) in top_connected
        println("  $skill: $count connections")
    end
    
    println("\n✓ Bidirectional awareness graph complete!")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
