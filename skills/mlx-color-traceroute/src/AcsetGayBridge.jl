"""
ACSets.jl ↔ Gay.jl ↔ JAX Bridge

Provides bidirectional interop between:
- ACSets.jl (categorical databases)
- Gay.jl (deterministic color generation)
- JAX (parallel compute via JSON export)

Usage:
    using ACSets, Gay
    include("AcsetGayBridge.jl")
    
    acset = world_color_traceroute(0x42D, servers)
    export_for_jax(acset, "/tmp/traceroute.json")
"""

module AcsetGayBridge

using JSON3
using UUIDs: uuid4

# ═══════════════════════════════════════════════════════════════════════════
# SplitMix64 (matches Gay.jl and jax_acset_gay.py exactly)
# ═══════════════════════════════════════════════════════════════════════════

function splitmix64(z::UInt64)::UInt64
    z = (z ⊻ (z >> 30)) * 0xBF58476D1CE4E5B9
    z = (z ⊻ (z >> 27)) * 0x94D049BB133111EB
    return z ⊻ (z >> 31)
end

function hop_color(seed::UInt64, idx::Int)
    state = splitmix64(seed ⊻ UInt64(idx))
    hue = (state % 65536) / 65536.0 * 360.0
    trit = Int(state % 3) - 1  # -1, 0, +1
    return (state=state, hue=hue, trit=trit, index=idx)
end

# ═══════════════════════════════════════════════════════════════════════════
# ACSet Schema for Color Traceroute
# ═══════════════════════════════════════════════════════════════════════════

# Schema definition (matches py-acsets format)
const COLOR_TRACEROUTE_SCHEMA = Dict(
    "name" => "ColorTraceroute",
    "obs" => ["Hop", "Agent", "Bridge"],
    "homs" => [
        Dict("name" => "next", "dom" => "Hop", "codom" => "Hop"),
        Dict("name" => "source", "dom" => "Bridge", "codom" => "Hop"),
        Dict("name" => "target", "dom" => "Bridge", "codom" => "Hop"),
        Dict("name" => "agent", "dom" => "Hop", "codom" => "Agent"),
    ],
    "attrs" => [
        Dict("name" => "seed", "dom" => "Hop", "codom" => "UInt64"),
        Dict("name" => "index", "dom" => "Hop", "codom" => "Int"),
        Dict("name" => "hue", "dom" => "Hop", "codom" => "Float"),
        Dict("name" => "trit", "dom" => "Hop", "codom" => "Int"),
        Dict("name" => "server", "dom" => "Hop", "codom" => "String"),
        Dict("name" => "latency", "dom" => "Hop", "codom" => "Float"),
        
        Dict("name" => "agent_seed", "dom" => "Agent", "codom" => "UInt64"),
        Dict("name" => "agent_trit", "dom" => "Agent", "codom" => "Int"),
        Dict("name" => "agent_name", "dom" => "Agent", "codom" => "String"),
        
        Dict("name" => "bridge_color", "dom" => "Bridge", "codom" => "Float"),
        Dict("name" => "dimension", "dom" => "Bridge", "codom" => "Int"),
    ],
)

# ═══════════════════════════════════════════════════════════════════════════
# World Builder (NOT demo_!)
# ═══════════════════════════════════════════════════════════════════════════

struct ColorTracerouteWorld
    hops::Vector{NamedTuple}
    agents::Vector{NamedTuple}
    bridges::Vector{NamedTuple}
    seed::UInt64
    fingerprint::UInt64
end

Base.length(w::ColorTracerouteWorld) = length(w.hops) + length(w.agents) + length(w.bridges)

function Base.merge(w1::ColorTracerouteWorld, w2::ColorTracerouteWorld)
    ColorTracerouteWorld(
        vcat(w1.hops, w2.hops),
        vcat(w1.agents, w2.agents),
        vcat(w1.bridges, w2.bridges),
        w1.seed ⊻ w2.seed,
        w1.fingerprint ⊻ w2.fingerprint,
    )
end

"""
    world_color_traceroute(seed, servers; n_agents=27) -> ColorTracerouteWorld

Build a color traceroute world with parallel color generation.
Returns a persistent, composable structure.
"""
function world_color_traceroute(
    seed::Integer,
    servers::Vector{String};
    n_agents::Int=27
)::ColorTracerouteWorld
    seed = UInt64(seed)
    
    # Generate hop colors
    hops = map(enumerate(servers)) do (i, server)
        color = hop_color(seed, i - 1)
        (
            id = i,
            seed = seed,
            index = i - 1,
            hue = color.hue,
            trit = color.trit,
            server = server,
            latency = 1.0 + (i - 1) * log(i),
            state = color.state,
        )
    end
    
    # Generate triadic agents
    agents = map(1:n_agents) do i
        color = hop_color(seed, i + 999)  # Offset
        path = []
        n = i - 1
        for _ in 1:3
            push!(path, ["−", "○", "+"][n % 3 + 1])
            n = n ÷ 3
        end
        (
            id = i,
            agent_seed = color.state,
            agent_trit = color.trit,
            agent_name = join(reverse(path)),
        )
    end
    
    # Generate bridges
    bridges = map(1:length(hops)-1) do i
        src = hops[i]
        tgt = hops[i + 1]
        bridge_seed = src.state ⊻ tgt.state
        bridge_color = hop_color(bridge_seed, 0)
        (
            id = i,
            source = i,
            target = i + 1,
            bridge_color = bridge_color.hue,
            dimension = src.trit != tgt.trit ? 1 : 0,
        )
    end
    
    # Compute fingerprint
    fp = reduce(⊻, [h.state for h in hops]; init=UInt64(0))
    
    ColorTracerouteWorld(hops, agents, bridges, seed, fp)
end

# ═══════════════════════════════════════════════════════════════════════════
# GF(3) Conservation
# ═══════════════════════════════════════════════════════════════════════════

function check_gf3_conservation(world::ColorTracerouteWorld)
    hop_sum = sum(h.trit for h in world.hops)
    agent_sum = sum(a.agent_trit for a in world.agents)
    total = hop_sum + agent_sum
    
    (
        hop_trit_sum = hop_sum,
        agent_trit_sum = agent_sum,
        total_sum = total,
        mod_3 = mod(total, 3),
        balanced = mod(total, 3) == 0,
    )
end

# ═══════════════════════════════════════════════════════════════════════════
# JSON Export (Catlab/py-acsets compatible)
# ═══════════════════════════════════════════════════════════════════════════

function to_json(world::ColorTracerouteWorld)
    Dict(
        "schema" => COLOR_TRACEROUTE_SCHEMA,
        "tables" => Dict(
            "Hop" => Dict(
                "_id" => [h.id for h in world.hops],
                "seed" => [h.seed for h in world.hops],
                "index" => [h.index for h in world.hops],
                "hue" => [h.hue for h in world.hops],
                "trit" => [h.trit for h in world.hops],
                "server" => [h.server for h in world.hops],
                "latency" => [h.latency for h in world.hops],
            ),
            "Agent" => Dict(
                "_id" => [a.id for a in world.agents],
                "agent_seed" => [a.agent_seed for a in world.agents],
                "agent_trit" => [a.agent_trit for a in world.agents],
                "agent_name" => [a.agent_name for a in world.agents],
            ),
            "Bridge" => Dict(
                "_id" => [b.id for b in world.bridges],
                "source" => [b.source for b in world.bridges],
                "target" => [b.target for b in world.bridges],
                "bridge_color" => [b.bridge_color for b in world.bridges],
                "dimension" => [b.dimension for b in world.bridges],
            ),
        ),
        "fingerprint" => world.fingerprint,
    )
end

function export_for_jax(world::ColorTracerouteWorld, path::String)
    open(path, "w") do f
        JSON3.write(f, to_json(world))
    end
    path
end

function import_from_jax(path::String)::ColorTracerouteWorld
    data = JSON3.read(read(path, String))
    
    hops = map(1:length(data.tables.Hop._id)) do i
        (
            id = data.tables.Hop._id[i],
            seed = UInt64(data.tables.Hop.seed[i]),
            index = data.tables.Hop.index[i],
            hue = data.tables.Hop.hue[i],
            trit = data.tables.Hop.trit[i],
            server = data.tables.Hop.server[i],
            latency = data.tables.Hop.latency[i],
            state = UInt64(0),  # Recompute if needed
        )
    end
    
    agents = map(1:length(data.tables.Agent._id)) do i
        (
            id = data.tables.Agent._id[i],
            agent_seed = UInt64(data.tables.Agent.agent_seed[i]),
            agent_trit = data.tables.Agent.agent_trit[i],
            agent_name = data.tables.Agent.agent_name[i],
        )
    end
    
    bridges = map(1:length(data.tables.Bridge._id)) do i
        (
            id = data.tables.Bridge._id[i],
            source = data.tables.Bridge.source[i],
            target = data.tables.Bridge.target[i],
            bridge_color = data.tables.Bridge.bridge_color[i],
            dimension = data.tables.Bridge.dimension[i],
        )
    end
    
    seed = length(hops) > 0 ? hops[1].seed : UInt64(0)
    fp = get(data, :fingerprint, UInt64(0))
    
    ColorTracerouteWorld(hops, agents, bridges, seed, fp)
end

# ═══════════════════════════════════════════════════════════════════════════
# Visualization
# ═══════════════════════════════════════════════════════════════════════════

function render_traceroute(world::ColorTracerouteWorld)
    println("\n╔═══════════════════════════════════════════════════════════════╗")
    println("║  COLOR TRACEROUTE (ACSets.jl ↔ Gay.jl ↔ JAX)                  ║")
    println("║  Seed: 0x$(string(world.seed, base=16, pad=16))                ║")
    println("╚═══════════════════════════════════════════════════════════════╝\n")
    
    for hop in world.hops
        trit_sym = Dict(-1 => "−", 0 => "○", 1 => "+")[hop.trit]
        # ANSI color from hue
        h = hop.hue / 360
        r = round(Int, 255 * (1 - abs(h * 6 - 3) + 1) / 2)
        g = round(Int, 255 * (1 - abs(h * 6 - 2) + 1) / 2)
        b = round(Int, 255 * (1 - abs(h * 6 - 4) + 1) / 2)
        print("  $(hop.index)  ")
        print("\e[48;2;$(r);$(g);$(b)m  \e[0m  ")
        println("$(rpad(hop.server, 20)) $trit_sym  $(round(hop.latency, digits=3))ms")
    end
    
    gf3 = check_gf3_conservation(world)
    println()
    println("  GF(3): $(gf3.total_sum) ≡ $(gf3.mod_3) (mod 3)")
    if gf3.balanced
        println("  ✓ Triadic balance conserved")
    else
        println("  ○ Imbalanced")
    end
    
    println("\n  Fingerprint: 0x$(string(world.fingerprint, base=16, pad=16))")
end

# ═══════════════════════════════════════════════════════════════════════════
# Exports
# ═══════════════════════════════════════════════════════════════════════════

export ColorTracerouteWorld
export world_color_traceroute
export check_gf3_conservation
export export_for_jax, import_from_jax
export render_traceroute
export splitmix64, hop_color

end # module

# ═══════════════════════════════════════════════════════════════════════════
# Demo (run with: julia AcsetGayBridge.jl)
# ═══════════════════════════════════════════════════════════════════════════

if abspath(PROGRAM_FILE) == @__FILE__
    using .AcsetGayBridge
    
    servers = [
        "sRGB", "clojure-mcp", "nrepl-mcp-server", "grain/clj-dspy",
        "modex", "java-probe", "fastmlx", "Gay.jl/Rec2020", "metaphysics"
    ]
    
    world = world_color_traceroute(0x42D, servers; n_agents=27)
    render_traceroute(world)
    
    # Export for JAX
    path = export_for_jax(world, "/tmp/traceroute_julia.json")
    println("\n  Exported to: $path")
end
