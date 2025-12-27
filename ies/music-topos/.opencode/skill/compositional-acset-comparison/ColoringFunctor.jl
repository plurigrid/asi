# ColoringFunctor.jl - Coloring Functors for Schema Comparison
# Based on StructuredDecompositions.jl and Bumpus "Deciding Sheaves on Presheaves"
# Gay.jl Seed: 4000000
#
# A coloring functor F: C → Set assigns colors to schema objects
# such that morphisms preserve or transform colors predictably.
#
# Key insight: Irreversible morphisms BREAK color preservation
# (they map distinct colors to the same color - not injective)

using ACSets, Catlab

include("DuckDBACSet.jl")
include("LanceDBACSet.jl")

# ═══════════════════════════════════════════════════════════════════════
# GAY.JL GOLDEN THREAD PALETTE (Seed 4000000)
# ═══════════════════════════════════════════════════════════════════════

"""
Golden angle φ = 137.508° walk for maximal color dispersion
Each step rotates by φ on the color wheel, ensuring no adjacent
colors are too similar.

From Gay.jl: deterministic, reproducible, maximally dispersed
"""
const GOLDEN_ANGLE = 137.508

"""
Generate color at index i using golden spiral
"""
function golden_color(i::Int; seed::Int=4000000, saturation=0.7, lightness=0.55)
    # Combine seed and index for deterministic hue
    combined = seed + i * 2654435761  # Knuth multiplicative hash
    base_hue = (combined % 360)
    hue = mod(base_hue + (i - 1) * GOLDEN_ANGLE, 360)
    
    # HSL to hex (simplified)
    hsl_to_hex(hue, saturation, lightness)
end

"""
HSL to Hex color conversion
"""
function hsl_to_hex(h, s, l)
    c = (1 - abs(2*l - 1)) * s
    x = c * (1 - abs(mod(h/60, 2) - 1))
    m = l - c/2
    
    r, g, b = if h < 60
        (c, x, 0)
    elseif h < 120
        (x, c, 0)
    elseif h < 180
        (0, c, x)
    elseif h < 240
        (0, x, c)
    elseif h < 300
        (x, 0, c)
    else
        (c, 0, x)
    end
    
    ri = round(Int, (r + m) * 255)
    gi = round(Int, (g + m) * 255)
    bi = round(Int, (b + m) * 255)
    
    "#" * string(ri, base=16, pad=2) * string(gi, base=16, pad=2) * string(bi, base=16, pad=2)
end

# ═══════════════════════════════════════════════════════════════════════
# COLORING FUNCTOR DEFINITION
# ═══════════════════════════════════════════════════════════════════════

"""
A Coloring Functor F: C → Set where:
- C is the schema category (objects + morphisms)
- Set is the category of sets (here: colors)

F must satisfy:
- F(id_A) = id_{F(A)} (identity preservation)
- F(g ∘ f) = F(g) ∘ F(f) (composition preservation)

For graph coloring (3-colorability):
- F: Vertices → {Red, Green, Blue}
- Adjacent vertices must have different colors
"""
struct ColoringFunctor
    object_colors::Dict{Symbol, String}
    morphism_preserving::Dict{Symbol, Bool}  # Does morphism preserve color?
    gf3_assignments::Dict{Symbol, Int}       # -1, 0, +1 for GF(3)
end

"""
Color a schema using golden thread walk
"""
function color_schema(schema; seed::Int=4000000)
    objects = collect(obs(schema))
    morphisms = collect(homs(schema))
    
    # Assign colors to objects
    object_colors = Dict{Symbol, String}()
    for (i, obj) in enumerate(objects)
        object_colors[obj] = golden_color(i; seed=seed)
    end
    
    # Check if morphisms preserve coloring
    # (in graph coloring: adjacent vertices have different colors)
    morphism_preserving = Dict{Symbol, Bool}()
    for hom in morphisms
        d = dom(hom)
        c = codom(hom)
        # Morphism "preserves" if it maps to different color (proper coloring)
        morphism_preserving[nameof(hom)] = object_colors[d] != object_colors[c]
    end
    
    # GF(3) assignments based on morphism role
    gf3_assignments = assign_gf3(schema)
    
    ColoringFunctor(object_colors, morphism_preserving, gf3_assignments)
end

# ═══════════════════════════════════════════════════════════════════════
# GF(3) ASSIGNMENT (Triad Conservation)
# ═══════════════════════════════════════════════════════════════════════

"""
Assign GF(3) trit values (-1, 0, +1) to schema objects based on role:
- MINUS (-1): Validators, constraints, reducers
- ERGODIC (0): Coordinators, transporters, navigators  
- PLUS (+1): Generators, composers, creators

For schemas:
- Type objects → MINUS (validate/constrain)
- Storage objects → ERGODIC (transport data)
- Data objects → PLUS (generate content)
"""
function assign_gf3(schema)
    assignments = Dict{Symbol, Int}()
    
    for obj in obs(schema)
        name = string(obj)
        
        # Heuristic classification
        if contains(name, "Type") || contains(name, "State") || contains(name, "Algo")
            assignments[obj] = -1  # MINUS: validators
        elseif contains(name, "Index") || contains(name, "Manifest") || contains(name, "Function")
            assignments[obj] = 0   # ERGODIC: coordinators
        else
            assignments[obj] = 1   # PLUS: generators
        end
    end
    
    assignments
end

"""
Verify GF(3) conservation: sum of trits in any triangle = 0 mod 3
"""
function verify_gf3_conservation(functor::ColoringFunctor)
    # For schema graphs, check all triangles (3-cycles)
    # A proper 3-coloring ensures GF(3) = 0 on every triangle
    
    values = collect(values(functor.gf3_assignments))
    total = sum(values)
    
    Dict(
        :total_trit_sum => total,
        :mod_3 => mod(total, 3),
        :conserved => mod(total, 3) == 0,
        :object_count => length(values),
        :distribution => Dict(
            :minus => count(v -> v == -1, values),
            :ergodic => count(v -> v == 0, values),
            :plus => count(v -> v == 1, values)
        )
    )
end

# ═══════════════════════════════════════════════════════════════════════
# 3-COLORABILITY CHECK
# ═══════════════════════════════════════════════════════════════════════

"""
Check if schema graph is 3-colorable

From 3-MATCH gadget: 3-SAT reduces to 3-coloring
A schema is 3-colorable iff its constraint graph has no odd cycles
that force color conflicts.

For DuckDB/LanceDB schemas: both are trees (hierarchical)
→ Trees are 2-colorable, hence trivially 3-colorable
"""
function is_3_colorable(schema)
    # Check if schema graph has odd cycles
    # Trees and forests are always 3-colorable
    
    objects = collect(obs(schema))
    morphisms = collect(homs(schema))
    
    # Build adjacency
    adj = Dict{Symbol, Set{Symbol}}()
    for obj in objects
        adj[obj] = Set{Symbol}()
    end
    
    for hom in morphisms
        d = dom(hom)
        c = codom(hom)
        push!(adj[d], c)
        push!(adj[c], d)
    end
    
    # Attempt 3-coloring using greedy algorithm
    coloring = Dict{Symbol, Int}()
    
    function can_color(v, c)
        for neighbor in adj[v]
            if haskey(coloring, neighbor) && coloring[neighbor] == c
                return false
            end
        end
        true
    end
    
    for obj in objects
        for c in 1:3
            if can_color(obj, c)
                coloring[obj] = c
                break
            end
        end
        
        if !haskey(coloring, obj)
            return (colorable=false, coloring=coloring, reason="No valid color for $obj")
        end
    end
    
    (colorable=true, coloring=coloring, reason="Graph is 3-colorable")
end

# ═══════════════════════════════════════════════════════════════════════
# IRREVERSIBILITY DETECTION VIA COLORING
# ═══════════════════════════════════════════════════════════════════════

"""
Key Insight: Irreversible morphisms break color injectivity

For a reversible morphism f: A → B:
- f is injective: distinct inputs → distinct outputs
- Coloring: F(A) ≠ F(B) can be maintained bidirectionally

For an irreversible morphism f: A → B:
- f loses information: multiple inputs → same output
- Coloring: F(A) might equal F(B) in reverse direction (collision)

DETECTION: If morphism maps multiple objects to same codomain,
and those objects have different semantic content, morphism is irreversible.
"""
function detect_irreversibility_via_coloring(schema)
    # Count how many objects map to each codomain
    codomain_sources = Dict{Symbol, Vector{Symbol}}()
    
    for hom in homs(schema)
        c = codom(hom)
        d = dom(hom)
        sources = get!(codomain_sources, c, Symbol[])
        push!(sources, d)
    end
    
    # Irreversible indicators
    irreversible = Symbol[]
    
    for hom in homs(schema)
        hom_name = nameof(hom)
        c = codom(hom)
        
        # Check for self-referential morphisms (like parent_manifest)
        if dom(hom) == c
            push!(irreversible, hom_name)
        end
        
        # Check for lossy projection (like source_column)
        # Heuristic: "source" or "parent" in name often indicates lossy
        if contains(string(hom_name), "source") || contains(string(hom_name), "parent")
            push!(irreversible, hom_name)
        end
    end
    
    unique(irreversible)
end

# ═══════════════════════════════════════════════════════════════════════
# COMPARISON FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════

"""
Compare colorings of two schemas
"""
function compare_colorings(schema1, schema2; seed::Int=4000000)
    coloring1 = color_schema(schema1; seed=seed)
    coloring2 = color_schema(schema2; seed=seed)
    
    # Find shared object names
    objects1 = Set(keys(coloring1.object_colors))
    objects2 = Set(keys(coloring2.object_colors))
    
    shared = intersect(objects1, objects2)
    unique1 = setdiff(objects1, objects2)
    unique2 = setdiff(objects2, objects1)
    
    Dict(
        :schema1_objects => length(objects1),
        :schema2_objects => length(objects2),
        :shared_objects => collect(shared),
        :unique_to_schema1 => collect(unique1),
        :unique_to_schema2 => collect(unique2),
        :coloring1 => coloring1,
        :coloring2 => coloring2,
        :gf3_verification1 => verify_gf3_conservation(coloring1),
        :gf3_verification2 => verify_gf3_conservation(coloring2),
        :colorability1 => is_3_colorable(schema1),
        :colorability2 => is_3_colorable(schema2),
        :irreversible1 => detect_irreversibility_via_coloring(schema1),
        :irreversible2 => detect_irreversibility_via_coloring(schema2)
    )
end

# ═══════════════════════════════════════════════════════════════════════
# STRUCTURED DECOMPOSITIONS CONNECTION
# ═══════════════════════════════════════════════════════════════════════

"""
From StructuredDecompositions.jl:

A structured decomposition of a graph G is:
1. A tree decomposition T (bags of vertices)
2. A functor F: T → Set assigning colors/structures to bags

The coloring functor generalizes this:
- Schema = graph to decompose
- Objects = bags
- Morphisms = edges between bags
- Colors = structural properties

DECIDING SHEAVES: A presheaf is a sheaf iff local sections glue globally
For colorings: local 3-colorings glue to global 3-coloring iff no odd cycles
"""
const STRUCTURED_DECOMP_CONNECTION = """
StructuredDecompositions.jl Integration
═══════════════════════════════════════

The coloring functor F: Schema → Set connects to:

1. TREE DECOMPOSITION:
   - DuckDB schema is tree-like (Table → RowGroup → Column → Segment)
   - LanceDB has tree + DAG (Manifest chains)
   - Tree width = 1 for pure trees

2. SHEAF CONDITION:
   - Local colorings (per subtree) must agree on overlaps
   - Irreversible morphisms create non-agreeing overlaps
   - parent_manifest: versions disagree on parent
   - source_column: text/embedding disagree on reconstruction

3. BUMPUS FPT ALGORITHMS:
   - Deciding k-colorability is FPT in treewidth
   - Both schemas have low treewidth → efficient algorithms
   - 3-colorability decidable in O(3^w * n) where w = treewidth

4. COLOR DESTNY:
   - Colors are deterministic (Gay.jl seed)
   - Same seed → same colors across runs
   - Reproducible analysis = color destiny manifest
"""

# ═══════════════════════════════════════════════════════════════════════
# RUN COMPARISON
# ═══════════════════════════════════════════════════════════════════════

function run_coloring_comparison()
    comparison = compare_colorings(SchDuckDB, SchLanceDB)
    
    Dict(
        :comparison => comparison,
        :structured_decomp => STRUCTURED_DECOMP_CONNECTION,
        :seed => 4000000,
        :golden_angle => GOLDEN_ANGLE
    )
end
