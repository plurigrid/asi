# Graph Grafting as Combinatorial Complex
# Unifies: Queryable, Colorable, Derangeable, Graftable

module GraphGrafting

using Random

export GraftNode, GraftEdge, GraftComplex, graft!, query, color!, derange!, verify_gf3

# ══════════════════════════════════════════════════════════════════════════════
# Core Structures
# ══════════════════════════════════════════════════════════════════════════════

struct GraftNode
    id::Symbol
    trit::Int8        # GF(3): -1, 0, +1
    world::Symbol     # :baseline, :original, :golden
    depth::Int        # tree depth from root
end

struct GraftEdge
    src::Symbol
    dst::Symbol
    adhesion::Vector{String}  # shared skills at adhesion
    distance::Float64
end

mutable struct GraftComplex
    nodes::Dict{Symbol, GraftNode}
    edges::Vector{GraftEdge}
    root::Union{Symbol, Nothing}
    seed::UInt64
end

GraftComplex(seed::UInt64) = GraftComplex(Dict(), GraftEdge[], nothing, seed)

# ══════════════════════════════════════════════════════════════════════════════
# Graftable: Attach rooted tree at vertex
# ══════════════════════════════════════════════════════════════════════════════

function graft!(complex::GraftComplex, tree_root::GraftNode, attach_at::Symbol, adhesion::Vector{String})
    if isnothing(complex.root)
        complex.root = tree_root.id
    end
    
    complex.nodes[tree_root.id] = tree_root
    
    if haskey(complex.nodes, attach_at)
        parent = complex.nodes[attach_at]
        dist = abs(parent.trit - tree_root.trit) * 60.0  # hue distance
        push!(complex.edges, GraftEdge(attach_at, tree_root.id, adhesion, dist))
    end
    
    complex
end

# ══════════════════════════════════════════════════════════════════════════════
# Queryable: Tree-shape decision via bag decomposition
# ══════════════════════════════════════════════════════════════════════════════

function query(complex::GraftComplex, predicate::Function)
    matching = GraftNode[]
    for (id, node) in complex.nodes
        if predicate(node)
            push!(matching, node)
        end
    end
    matching
end

function query_by_trit(complex::GraftComplex, trit::Int8)
    query(complex, n -> n.trit == trit)
end

function query_by_world(complex::GraftComplex, world::Symbol)
    query(complex, n -> n.world == world)
end

function tree_shape(complex::GraftComplex)
    adj = Dict{Symbol, Vector{Symbol}}()
    for edge in complex.edges
        push!(get!(adj, edge.src, Symbol[]), edge.dst)
    end
    (root=complex.root, adjacency=adj, depth=max_depth(complex))
end

function max_depth(complex::GraftComplex)
    isempty(complex.nodes) ? 0 : maximum(n.depth for n in values(complex.nodes))
end

# ══════════════════════════════════════════════════════════════════════════════
# Colorable: GF(3) 3-coloring
# ══════════════════════════════════════════════════════════════════════════════

function color!(complex::GraftComplex)
    rng = Random.MersenneTwister(complex.seed)
    for (id, node) in complex.nodes
        if node.trit == 0  # unassigned
            new_trit = rand(rng, [-1, 0, 1])
            complex.nodes[id] = GraftNode(node.id, Int8(new_trit), node.world, node.depth)
        end
    end
    complex
end

function verify_gf3(complex::GraftComplex)
    total = sum(n.trit for n in values(complex.nodes))
    (conserved = mod(total, 3) == 0, sum = total)
end

function trit_partition(complex::GraftComplex)
    minus = query_by_trit(complex, Int8(-1))
    ergodic = query_by_trit(complex, Int8(0))
    plus = query_by_trit(complex, Int8(1))
    (minus=minus, ergodic=ergodic, plus=plus)
end

# ══════════════════════════════════════════════════════════════════════════════
# Derangeable: Permutations with no fixed points
# ══════════════════════════════════════════════════════════════════════════════

function derange!(complex::GraftComplex)
    nodes = collect(values(complex.nodes))
    n = length(nodes)
    n < 2 && return complex
    
    rng = Random.MersenneTwister(complex.seed)
    
    ids = [n.id for n in nodes]
    perm = shuffle(rng, ids)
    
    while any(perm[i] == ids[i] for i in 1:n)
        perm = shuffle(rng, ids)
    end
    
    new_nodes = Dict{Symbol, GraftNode}()
    for i in 1:n
        old_node = complex.nodes[ids[i]]
        new_id = perm[i]
        new_nodes[ids[i]] = GraftNode(new_id, old_node.trit, old_node.world, old_node.depth)
    end
    
    complex.nodes = new_nodes
    complex
end

function is_derangement(complex::GraftComplex)
    for (id, node) in complex.nodes
        if id == node.id
            return false
        end
    end
    true
end

# ══════════════════════════════════════════════════════════════════════════════
# Combinatorial Complex Operations
# ══════════════════════════════════════════════════════════════════════════════

function compose(c1::GraftComplex, c2::GraftComplex, adhesion_vertex::Symbol)
    result = GraftComplex(c1.seed ⊻ c2.seed)
    
    for (id, node) in c1.nodes
        result.nodes[id] = node
    end
    for (id, node) in c2.nodes
        result.nodes[id] = node
    end
    
    append!(result.edges, c1.edges)
    append!(result.edges, c2.edges)
    
    if haskey(c1.nodes, adhesion_vertex) && !isnothing(c2.root)
        adhesion = ["graft_composition"]
        push!(result.edges, GraftEdge(adhesion_vertex, c2.root, adhesion, 0.0))
    end
    
    result.root = c1.root
    result
end

function euler_characteristic(complex::GraftComplex)
    v = length(complex.nodes)
    e = length(complex.edges)
    v - e  # χ = V - E for tree/forest
end

# ══════════════════════════════════════════════════════════════════════════════
# Demo
# ══════════════════════════════════════════════════════════════════════════════

function demo()
    println("═══ Graph Grafting Combinatorial Complex ═══")
    
    c = GraftComplex(UInt64(1069))
    
    root = GraftNode(:pr18, Int8(0), :golden, 0)
    alice = GraftNode(:alice, Int8(-1), :baseline, 1)
    bob = GraftNode(:bob, Int8(1), :original, 1)
    
    graft!(c, root, :none, String[])
    graft!(c, alice, :pr18, ["aptos-wallet-mcp"])
    graft!(c, bob, :pr18, ["aptos-wallet-mcp"])
    
    println("Tree shape: ", tree_shape(c))
    println("GF(3) check: ", verify_gf3(c))
    println("Trit partition: ", trit_partition(c))
    println("Euler χ: ", euler_characteristic(c))
    
    println("\nQuery by world :baseline:")
    for n in query_by_world(c, :baseline)
        println("  ", n)
    end
    
    c
end

end # module
