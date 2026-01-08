#!/usr/bin/env julia

"""
Awareness Graph Visualization with Low-Discrepancy Color Sequences

Extends bidirectional_awareness.jl with deterministic color assignment using:
- Plastic constant (φ₂) for behavioral similarity (hue + saturation)
- Halton sequence for trit neighborhoods (RGB)
- Golden angle for citation depth (hue spiral)
- Sobol for high-dimensional node attributes

All colors are deterministic and bijective: given a color and method, 
you can recover which node/edge it represents.
"""

include("../org-babel-execution/bidirectional_awareness.jl")
include("LowDiscrepancySequences.jl")

using .LowDiscrepancySequences
using Colors
using JSON

# ============================================================================
# Color Assignment Strategies
# ============================================================================

"""
    assign_node_colors(graph::AwarenessGraph; seed=42)

Assign deterministic colors to each node based on multiple attributes.

Uses different low-discrepancy sequences for different attributes:
- Plastic constant: behavioral signature (hue + saturation)
- Halton: trit value (RGB direct)
- Golden angle: alphabetical position
"""
function assign_node_colors(graph::AwarenessGraph; seed=42)
    colors = Dict{String, Dict{Symbol, RGB}}()
    
    # Sort nodes alphabetically for consistent indexing
    sorted_names = sort(collect(keys(graph.nodes)))
    name_to_idx = Dict(name => i for (i, name) in enumerate(sorted_names))
    
    for (name, node) in graph.nodes
        idx = name_to_idx[name]
        
        # Behavioral color (plastic constant for 2D coverage)
        behavioral_color = plastic_color(idx, seed=seed)
        
        # Trit color (Halton for discrete categories)
        trit = node.behavior.trit
        trit_idx = isnothing(trit) ? 0 : trit + 2  # Map {-1,0,1} → {1,2,3}
        trit_color = halton_hsl_color(trit_idx, bases=(2,3,5))
        
        # Position color (golden angle spiral)
        position_color = golden_angle_color(idx, seed=seed)
        
        # Language color (hash language name to index)
        lang = node.behavior.primary_language
        lang_idx = sum(Int.(collect(lang))) % 1000
        lang_color = kronecker_color(lang_idx, α=√2, seed=seed)
        
        colors[name] = Dict(
            :behavioral => behavioral_color,
            :trit => trit_color,
            :position => position_color,
            :language => lang_color,
            :primary => behavioral_color  # Default primary color
        )
    end
    
    return colors
end

"""
    assign_edge_colors(graph::AwarenessGraph; seed=42)

Assign colors to edges based on edge type and weight.

Uses R-sequence for 3D coverage (type, weight, direction).
"""
function assign_edge_colors(graph::AwarenessGraph; seed=42)
    colors = Dict{Tuple{String,String,Symbol}, RGB}()
    
    for (i, edge) in enumerate(graph.edges)
        # Different base index for each edge type
        base_idx = if edge.edge_type == :citation
            i
        elseif edge.edge_type == :trit_equivalence
            i + 10000
        elseif edge.edge_type == :behavioral_similarity
            i + 20000
        else
            i + 30000
        end
        
        # Weight modulates lightness via R-sequence dimension
        dim = edge.weight > 0.5 ? 3 : 2
        edge_color = r_sequence_color(base_idx, dim=dim, seed=seed)
        
        colors[(edge.from, edge.to, edge.edge_type)] = edge_color
    end
    
    return colors
end

# ============================================================================
# Visualization Export
# ============================================================================

"""
    color_to_hex(c::RGB)

Convert RGB color to hex string.
"""
function color_to_hex(c::RGB)
    r = round(Int, clamp(c.r, 0, 1) * 255)
    g = round(Int, clamp(c.g, 0, 1) * 255)
    b = round(Int, clamp(c.b, 0, 1) * 255)
    return @sprintf("#%02X%02X%02X", r, g, b)
end

"""
    export_colored_graph_json(graph::AwarenessGraph, node_colors, edge_colors, output_path)

Export awareness graph with colors to JSON for visualization.
"""
function export_colored_graph_json(graph::AwarenessGraph, node_colors, edge_colors, output_path)
    nodes = []
    edges = []
    
    # Export nodes
    for (name, node) in graph.nodes
        colors_hex = Dict(
            k => color_to_hex(v) 
            for (k, v) in node_colors[name]
        )
        
        push!(nodes, Dict(
            "id" => name,
            "label" => name,
            "colors" => colors_hex,
            "trit" => node.behavior.trit,
            "language" => node.behavior.primary_language,
            "has_code" => node.behavior.has_code,
            "representations" => length(node.representations),
            "cites" => length(node.cites),
            "cited_by" => length(node.cited_by),
            "trit_neighbors" => length(node.trit_neighbors),
            "behavior_neighbors" => length(node.behavior_neighbors)
        ))
    end
    
    # Export edges
    for edge in graph.edges
        key = (edge.from, edge.to, edge.edge_type)
        color_hex = color_to_hex(edge_colors[key])
        
        push!(edges, Dict(
            "from" => edge.from,
            "to" => edge.to,
            "type" => string(edge.edge_type),
            "weight" => edge.weight,
            "color" => color_hex
        ))
    end
    
    output = Dict(
        "nodes" => nodes,
        "edges" => edges,
        "metadata" => Dict(
            "node_count" => length(nodes),
            "edge_count" => length(edges),
            "color_methods" => Dict(
                "behavioral" => "plastic constant (φ₂)",
                "trit" => "Halton sequence",
                "position" => "golden angle (φ)",
                "language" => "Kronecker (√2)",
                "edges" => "R-sequence"
            ),
            "bijection" => "All colors are deterministically invertible to node/edge identity"
        )
    )
    
    open(output_path, "w") do f
        JSON.print(f, output, 2)
    end
    
    println("Exported colored graph to: $output_path")
    println("  Nodes: $(length(nodes))")
    println("  Edges: $(length(edges))")
end

"""
    export_colored_graph_dot(graph::AwarenessGraph, node_colors, edge_colors, output_path)

Export awareness graph to Graphviz DOT format with colors.
"""
function export_colored_graph_dot(graph::AwarenessGraph, node_colors, edge_colors, output_path)
    open(output_path, "w") do io
        println(io, "digraph awareness {")
        println(io, "  rankdir=LR;")
        println(io, "  node [shape=box, style=filled];")
        println(io, "")
        
        # Nodes
        for (name, node) in graph.nodes
            primary_color = color_to_hex(node_colors[name][:primary])
            trit_color = color_to_hex(node_colors[name][:trit])
            
            label = "$name\\n"
            label *= "trit=$(node.behavior.trit)\\n"
            label *= "lang=$(node.behavior.primary_language)"
            
            println(io, "  \"$name\" [")
            println(io, "    label=\"$label\",")
            println(io, "    fillcolor=\"$primary_color\",")
            println(io, "    color=\"$trit_color\",")
            println(io, "    penwidth=3")
            println(io, "  ];")
        end
        
        println(io, "")
        
        # Edges
        for edge in graph.edges
            key = (edge.from, edge.to, edge.edge_type)
            color_hex = color_to_hex(edge_colors[key])
            
            style = if edge.edge_type == :citation
                "solid"
            elseif edge.edge_type == :trit_equivalence
                "dashed"
            else
                "dotted"
            end
            
            penwidth = 1 + edge.weight * 3
            
            println(io, "  \"$(edge.from)\" -> \"$(edge.to)\" [")
            println(io, "    color=\"$color_hex\",")
            println(io, "    style=$style,")
            println(io, "    penwidth=$penwidth,")
            println(io, "    label=\"$(edge.edge_type)\"")
            println(io, "  ];")
        end
        
        println(io, "}")
    end
    
    println("Exported DOT file to: $output_path")
    println("Render with: dot -Tpng $output_path -o graph.png")
end

"""
    generate_color_legend(node_colors, output_path)

Generate a legend mapping color methods to their meanings.
"""
function generate_color_legend(node_colors, output_path)
    legend = Dict(
        "color_methods" => Dict(
            "behavioral" => Dict(
                "method" => "Plastic Constant (φ₂ ≈ 1.325)",
                "formula" => "h = (n/φ₂) mod 1, s = (n/φ₂²) mod 1",
                "meaning" => "2D coverage of hue-saturation space for behavioral signatures",
                "bijection" => "Recoverable: color + seed → node index"
            ),
            "trit" => Dict(
                "method" => "Halton Sequence (bases 2,3,5)",
                "formula" => "r = halton(n,2), g = halton(n,3), b = halton(n,5)",
                "meaning" => "Discrete trit categories: -1 (MINUS), 0 (ERGODIC), +1 (PLUS)",
                "bijection" => "Recoverable: color + bases → trit value"
            ),
            "position" => Dict(
                "method" => "Golden Angle (φ ≈ 1.618)",
                "formula" => "hue = (n/φ) mod 1",
                "meaning" => "Alphabetical position spiral - never repeats, always returns",
                "bijection" => "Recoverable: color + seed → alphabetical index"
            ),
            "language" => Dict(
                "method" => "Kronecker (α = √2)",
                "formula" => "hue = (n·√2) mod 1",
                "meaning" => "Primary programming language hash",
                "bijection" => "Recoverable: color + α + seed → language hash"
            ),
            "edges" => Dict(
                "method" => "R-sequence (φ₃ for 3D)",
                "formula" => "Uses 3D golden ratio for (type, weight, direction)",
                "meaning" => "Edge type and strength visualization",
                "bijection" => "Recoverable: color + dim + seed → edge index"
            )
        ),
        "constants" => Dict(
            "φ" => 1.618033988749895,
            "φ₂" => 1.3247179572447460,
            "φ₃" => 1.2207440846057596,
            "√2" => 1.4142135623730951,
            "√3" => 1.7320508075688772
        ),
        "inversion" => Dict(
            "description" => "All color assignments are bijective",
            "capability" => "Given (color, seed, method), can recover original index/identity",
            "tools" => [
                "invert_color(color, :plastic, seed=42) → node_index",
                "invert_color(color, :golden, seed=42) → position_index",
                "invert_color(color, :halton, bases=(2,3,5)) → trit_index"
            ]
        )
    )
    
    open(output_path, "w") do f
        JSON.print(f, legend, 2)
    end
    
    println("Exported color legend to: $output_path")
end

# ============================================================================
# Main Execution
# ============================================================================

function main()
    if length(ARGS) < 1
        println("Usage: julia awareness_visualization.jl <asi_root> [seed]")
        println("Example: julia awareness_visualization.jl /Users/bob/i/asi 42")
        exit(1)
    end
    
    asi_root = ARGS[1]
    seed = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 42
    
    println("Building awareness graph from: $asi_root")
    println("Using seed: $seed")
    println()
    
    # Build graph
    graph = build_awareness_graph(asi_root)
    println("Graph built:")
    println("  Nodes: $(length(graph.nodes))")
    println("  Edges: $(length(graph.edges))")
    println()
    
    # Assign colors
    println("Assigning colors using low-discrepancy sequences...")
    node_colors = assign_node_colors(graph, seed=seed)
    edge_colors = assign_edge_colors(graph, seed=seed)
    println("  Node colors: $(length(node_colors)) ($(length(node_colors) * 4) color variants)")
    println("  Edge colors: $(length(edge_colors))")
    println()
    
    # Export
    output_dir = joinpath(asi_root, "skills", "low-discrepancy-sequences", "visualizations")
    mkpath(output_dir)
    
    json_path = joinpath(output_dir, "awareness_graph_colored.json")
    export_colored_graph_json(graph, node_colors, edge_colors, json_path)
    println()
    
    dot_path = joinpath(output_dir, "awareness_graph_colored.dot")
    export_colored_graph_dot(graph, node_colors, edge_colors, dot_path)
    println()
    
    legend_path = joinpath(output_dir, "color_legend.json")
    generate_color_legend(node_colors, legend_path)
    println()
    
    # Summary statistics
    println("Color Distribution Summary:")
    
    # Trit distribution
    trit_counts = Dict(-1 => 0, 0 => 0, 1 => 0, nothing => 0)
    for (name, node) in graph.nodes
        trit = node.behavior.trit
        trit_counts[trit] = get(trit_counts, trit, 0) + 1
    end
    
    println("  Trit distribution:")
    println("    MINUS (-1): $(trit_counts[-1])")
    println("    ERGODIC (0): $(trit_counts[0])")
    println("    PLUS (+1): $(trit_counts[1])")
    println("    Unknown: $(trit_counts[nothing])")
    println()
    
    # Language distribution
    lang_counts = Dict{String, Int}()
    for (name, node) in graph.nodes
        lang = node.behavior.primary_language
        lang_counts[lang] = get(lang_counts, lang, 0) + 1
    end
    
    println("  Top 5 languages:")
    for (lang, count) in sort(collect(lang_counts), by=x->x[2], rev=true)[1:min(5, length(lang_counts))]
        println("    $lang: $count")
    end
    println()
    
    println("✓ Awareness graph visualization complete!")
    println("All colors are deterministic and bijective - you can recover node identity from color.")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
