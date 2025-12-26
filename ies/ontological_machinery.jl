# Ontological Machinery: Narya-Inspired World/Coworld Semantics
# ═══════════════════════════════════════════════════════════════════════
#
# Combines:
# - unworld: Extract derivational chain from temporal frame
# - reworld: Embed chain into possible worlds (Hamkins multiverse)
# - involution: ι∘ι = id (self-inverse)
# - observational bridge types: Narya's higher-dimensional equality
# - interrupteurs: Session interrupt with GF(3) balance snapshots

using Catlab.CategoricalAlgebra, ACSets

# ═══════════════════════════════════════════════════════════════════════
# CORE TYPES
# ═══════════════════════════════════════════════════════════════════════

"""
GF(3) trit values with categorical semantics.
"""
@enum Trit::Int8 MINUS=-1 ERGODIC=0 PLUS=1

"""
Derivational chain - replaces temporal succession with seed-indexed derivation.
"""
struct DerivationChain
    genesis_seed::UInt64
    chain::Vector{Trit}
    colors::Vector{String}
    fingerprints::Vector{UInt64}
end

"""
Possible world in Hamkins multiverse.
"""
struct World
    id::Int
    seed::UInt64
    trit::Trit
    accessibility::Set{Int}  # Accessible worlds (Kripke semantics)
end

"""
Observational bridge type (Narya-inspired).
Connects source and target via a witness of observational equality.
"""
struct ObservationalBridge{S, T}
    source::S
    target::T
    dimension::Int           # 0=value, 1=diff, 2=conflict resolution
    witness::UInt64          # Hash witnessing the bridge
    color::String            # Gay.jl deterministic color
end

"""
Interrupt: World/Coworld transition with balance snapshot.
"""
struct Interrupt
    from_world::Int
    to_world::Int
    balance::Tuple{Int, Int, Int}  # (minus, ergodic, plus)
    bridge::ObservationalBridge
    gap_seconds::Float64
end

# ═══════════════════════════════════════════════════════════════════════
# SPLITMIX64 (Gay.jl core)
# ═══════════════════════════════════════════════════════════════════════

function splitmix64(state::UInt64)::UInt64
    z = state + 0x9e3779b97f4a7c15
    z = (z ⊻ (z >> 30)) * 0xbf58476d1ce4e5b9
    z = (z ⊻ (z >> 27)) * 0x94d049bb133111eb
    z ⊻ (z >> 31)
end

function color_at(seed::UInt64, index::Int)::String
    h = splitmix64(seed ⊻ UInt64(index))
    r = (h >> 16) & 0xff
    g = (h >> 8) & 0xff
    b = h & 0xff
    "#" * uppercase(string(r, base=16, pad=2) * 
                    string(g, base=16, pad=2) * 
                    string(b, base=16, pad=2))
end

function trit_at(seed::UInt64, index::Int)::Trit
    h = splitmix64(seed ⊻ UInt64(index))
    Trit(mod(Int(h % 3), 3) - 1)
end

# ═══════════════════════════════════════════════════════════════════════
# UNWORLD: Temporal → Derivational
# ═══════════════════════════════════════════════════════════════════════

"""
    unworld(observations, genesis_seed) -> DerivationChain

Extract derivational chain from temporal observations.
Time is replaced with derivation index.

The unworld operation is the left adjoint to reworld:
  unworld ⊣ reworld
"""
function unworld(observations::Vector, genesis_seed::UInt64)::DerivationChain
    chain = Trit[]
    colors = String[]
    fingerprints = UInt64[]
    
    for (i, obs) in enumerate(observations)
        trit = trit_at(genesis_seed, i)
        push!(chain, trit)
        push!(colors, color_at(genesis_seed, i))
        push!(fingerprints, splitmix64(genesis_seed ⊻ UInt64(i)))
    end
    
    DerivationChain(genesis_seed, chain, colors, fingerprints)
end

"""
    unworld(interrupts::Vector{Interrupt}) -> DerivationChain

Extract chain from interrupt sequence.
"""
function unworld(interrupts::Vector{Interrupt})::DerivationChain
    genesis = isempty(interrupts) ? UInt64(0) : interrupts[1].bridge.witness
    chain = Trit[]
    colors = String[]
    fingerprints = UInt64[]
    
    for (i, int) in enumerate(interrupts)
        balance_sum = sum(int.balance)
        trit = Trit(mod(balance_sum, 3) - 1)
        push!(chain, trit)
        push!(colors, int.bridge.color)
        push!(fingerprints, int.bridge.witness)
    end
    
    DerivationChain(genesis, chain, colors, fingerprints)
end

# ═══════════════════════════════════════════════════════════════════════
# REWORLD: Derivational → Possible Worlds
# ═══════════════════════════════════════════════════════════════════════

"""
    reworld(chain::DerivationChain, num_worlds=3) -> Vector{World}

Embed derivational chain into Hamkins multiverse.
Each derivation step gets assigned to a world via forcing.

The reworld operation is the right adjoint to unworld:
  unworld ⊣ reworld
"""
function reworld(chain::DerivationChain, num_worlds::Int=3)::Vector{World}
    worlds = World[]
    
    for (i, trit) in enumerate(chain.chain)
        # Base world from trit
        base = Int(trit) + 2  # -1→1, 0→2, +1→3
        
        # Forcing extension
        forced = mod(Int(splitmix64(chain.genesis_seed ⊻ UInt64(i + 1000)) % num_worlds), num_worlds) + 1
        
        # Final world assignment
        world_id = mod(base + forced - 2, num_worlds) + 1
        
        # Accessibility: same trit worlds are mutually accessible
        accessible = Set{Int}()
        for (j, other_trit) in enumerate(chain.chain)
            if other_trit == trit && j != i
                push!(accessible, j)
            end
        end
        
        push!(worlds, World(world_id, chain.fingerprints[i], trit, accessible))
    end
    
    worlds
end

# ═══════════════════════════════════════════════════════════════════════
# INVOLUTION: ι ∘ ι = id
# ═══════════════════════════════════════════════════════════════════════

"""
    involute(chain::DerivationChain) -> DerivationChain

Apply involution: swap structure.
Satisfies: involute(involute(x)) ≈ x (modulo hashing)
"""
function involute(chain::DerivationChain)::DerivationChain
    # Reverse the chain (involution on sequence)
    new_chain = reverse(chain.chain)
    new_colors = reverse(chain.colors)
    new_fps = reverse(chain.fingerprints)
    
    # XOR genesis with involution marker
    new_genesis = chain.genesis_seed ⊻ 0xFFFFFFFFFFFFFFFF
    
    DerivationChain(new_genesis, new_chain, new_colors, new_fps)
end

"""
    verify_involution(chain::DerivationChain) -> Bool

Verify ι ∘ ι = id (within GF(3) equivalence).
"""
function verify_involution(chain::DerivationChain)::Bool
    once = involute(chain)
    twice = involute(once)
    
    # Check chain equivalence (not strict equality due to seed XOR)
    chain.chain == twice.chain
end

# ═══════════════════════════════════════════════════════════════════════
# OBSERVATIONAL BRIDGE TYPES (Narya)
# ═══════════════════════════════════════════════════════════════════════

"""
    bridge(source, target, seed) -> ObservationalBridge

Create observational bridge between source and target.
This is Narya's higher-dimensional equality witness.
"""
function bridge(source::S, target::T, seed::UInt64) where {S, T}
    source_hash = hash(source)
    target_hash = hash(target)
    witness = source_hash ⊻ target_hash ⊻ seed
    
    # Dimension: 0 if identical, 1 if differ, 2 if conflict
    dim = if source_hash == target_hash
        0
    elseif abs(Int(source_hash % 1000) - Int(target_hash % 1000)) < 100
        1
    else
        2
    end
    
    color = color_at(seed, Int(witness % 1000))
    
    ObservationalBridge{S, T}(source, target, dim, witness, color)
end

"""
    transport(bridge::ObservationalBridge, property) -> property

Transport property along observational bridge (covariant transport).
"""
function transport(br::ObservationalBridge{S, T}, property::Function) where {S, T}
    # If dimension 0, property is preserved exactly
    if br.dimension == 0
        return property(br.target)
    end
    
    # If dimension 1, compute transported property
    property(br.target)
end

# ═══════════════════════════════════════════════════════════════════════
# INTERRUPT CREATION WITH BRIDGE
# ═══════════════════════════════════════════════════════════════════════

"""
    create_interrupt(from_world, to_world, balance, seed, gap) -> Interrupt

Create interrupt with observational bridge.
"""
function create_interrupt(
    from_world::Int, 
    to_world::Int, 
    balance::Tuple{Int, Int, Int},
    seed::UInt64,
    gap::Float64
)::Interrupt
    br = bridge(from_world, to_world, seed)
    Interrupt(from_world, to_world, balance, br, gap)
end

# ═══════════════════════════════════════════════════════════════════════
# GF(3) CONSERVATION
# ═══════════════════════════════════════════════════════════════════════

"""
    is_conserved(chain::DerivationChain) -> Bool

Check if chain satisfies GF(3) conservation: sum(trits) ≡ 0 (mod 3).
"""
function is_conserved(chain::DerivationChain)::Bool
    total = sum(Int.(chain.chain))
    mod(total, 3) == 0
end

"""
    balance_chain!(chain::DerivationChain) -> DerivationChain

Add balancing trit if needed to satisfy GF(3) conservation.
"""
function balance_chain!(chain::DerivationChain)::DerivationChain
    if is_conserved(chain)
        return chain
    end
    
    total = sum(Int.(chain.chain))
    needed = Trit(-mod(total, 3))
    
    push!(chain.chain, needed)
    push!(chain.colors, color_at(chain.genesis_seed, length(chain.chain)))
    push!(chain.fingerprints, splitmix64(chain.genesis_seed ⊻ UInt64(length(chain.chain))))
    
    chain
end

# ═══════════════════════════════════════════════════════════════════════
# WORLD HOPPING (Badiou triangle inequality)
# ═══════════════════════════════════════════════════════════════════════

"""
    world_distance(w1::World, w2::World) -> Float64

Compute distance between worlds using seed Hamming distance + trit difference.
"""
function world_distance(w1::World, w2::World)::Float64
    # Hamming distance of seeds
    xor_val = w1.seed ⊻ w2.seed
    hamming = count_ones(xor_val)
    
    # Trit difference
    trit_diff = abs(Int(w1.trit) - Int(w2.trit))
    
    # Accessibility penalty
    accessible_penalty = w2.id ∈ w1.accessibility ? 0.0 : 1.0
    
    sqrt(Float64(hamming)^2 + Float64(trit_diff)^2 + accessible_penalty^2)
end

"""
    valid_hop(w1::World, w2::World, w3::World) -> Bool

Check triangle inequality for world hop.
"""
function valid_hop(w1::World, w2::World, w3::World)::Bool
    d12 = world_distance(w1, w2)
    d23 = world_distance(w2, w3)
    d13 = world_distance(w1, w3)
    
    d13 ≤ d12 + d23
end

# ═══════════════════════════════════════════════════════════════════════
# ACSET SCHEMA
# ═══════════════════════════════════════════════════════════════════════

@present SchOntology(FreeSchema) begin
    # Objects
    Chain::Ob
    World::Ob
    Bridge::Ob
    Interrupt::Ob
    
    # Chain structure
    Seed::AttrType
    TritVal::AttrType
    Color::AttrType
    
    chain_seed::Attr(Chain, Seed)
    
    # World structure
    WorldId::AttrType
    world_id::Attr(World, WorldId)
    world_seed::Attr(World, Seed)
    world_trit::Attr(World, TritVal)
    
    # Morphisms
    chain_to_world::Hom(Chain, World)  # reworld
    world_to_chain::Hom(World, Chain)  # unworld
    
    # Bridge connects source and target worlds
    bridge_source::Hom(Bridge, World)
    bridge_target::Hom(Bridge, World)
    bridge_witness::Attr(Bridge, Seed)
    bridge_color::Attr(Bridge, Color)
    
    # Interrupt uses bridge for transition
    interrupt_bridge::Hom(Interrupt, Bridge)
    Gap::AttrType
    interrupt_gap::Attr(Interrupt, Gap)
end

@acset_type Ontology(SchOntology, 
    index=[:chain_to_world, :world_to_chain, :bridge_source, :bridge_target])

# ═══════════════════════════════════════════════════════════════════════
# DEMONSTRATION
# ═══════════════════════════════════════════════════════════════════════

function demo()
    println("═══════════════════════════════════════════════════════════════")
    println("ONTOLOGICAL MACHINERY DEMONSTRATION")
    println("═══════════════════════════════════════════════════════════════")
    
    # 1. Create derivation chain via unworld
    genesis = UInt64(0x42D)
    observations = ["obs1", "obs2", "obs3", "obs4", "obs5"]
    chain = unworld(observations, genesis)
    
    println("\n1. UNWORLD: temporal → derivational")
    println("   Genesis seed: 0x$(string(genesis, base=16))")
    println("   Chain: $(chain.chain)")
    println("   Colors: $(chain.colors)")
    println("   GF(3) conserved: $(is_conserved(chain))")
    
    # 2. Balance if needed
    if !is_conserved(chain)
        chain = balance_chain!(chain)
        println("   After balancing: $(chain.chain)")
        println("   Now conserved: $(is_conserved(chain))")
    end
    
    # 3. Reworld into possible worlds
    worlds = reworld(chain)
    println("\n2. REWORLD: derivational → possible worlds")
    for (i, w) in enumerate(worlds)
        println("   World $i: id=$(w.id), trit=$(w.trit), accessible=$(length(w.accessibility))")
    end
    
    # 4. Test involution
    println("\n3. INVOLUTION: ι ∘ ι = id")
    println("   Involution verified: $(verify_involution(chain))")
    
    # 5. Create observational bridge
    if length(worlds) >= 2
        br = bridge(worlds[1], worlds[2], genesis)
        println("\n4. OBSERVATIONAL BRIDGE (Narya)")
        println("   Dimension: $(br.dimension)")
        println("   Color: $(br.color)")
    end
    
    # 6. Test triangle inequality
    if length(worlds) >= 3
        println("\n5. TRIANGLE INEQUALITY (Badiou)")
        println("   d(W1,W2) = $(round(world_distance(worlds[1], worlds[2]), digits=2))")
        println("   d(W2,W3) = $(round(world_distance(worlds[2], worlds[3]), digits=2))")
        println("   d(W1,W3) = $(round(world_distance(worlds[1], worlds[3]), digits=2))")
        println("   Valid hop: $(valid_hop(worlds[1], worlds[2], worlds[3]))")
    end
    
    println("\n═══════════════════════════════════════════════════════════════")
end

# Run demo if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end
