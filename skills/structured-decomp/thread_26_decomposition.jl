# Thread 26-Decomposition: Distill Amp Threads into 26 Worlds
# Using StructuredDecompositions.jl sheaf-theoretic gluing
#
# Each world (A-Z) is a bag in the decomposition.
# Adhesions preserve GF(3) conservation across world boundaries.

using Random

# ══════════════════════════════════════════════════════════════════════════════
# 26 World Trit Assignments (balanced: 9 PLUS + 8 ERGODIC + 9 MINUS = 0)
# ══════════════════════════════════════════════════════════════════════════════

const WORLDS_26 = Dict{Char, Int8}(
    # PLUS (+1): Synthesis/Generation - 9 worlds
    'A' => 1, 'D' => 1, 'F' => 1, 'H' => 1, 'J' => 1,
    'M' => 1, 'P' => 1, 'U' => 1, 'Y' => 1,
    
    # ERGODIC (0): Coordination/Balance - 8 worlds  
    'E' => 0, 'G' => 0, 'I' => 0, 'N' => 0, 'O' => 0,
    'R' => 0, 'S' => 0, 'X' => 0,
    
    # MINUS (-1): Analysis/Verification - 9 worlds
    'B' => -1, 'C' => -1, 'K' => -1, 'L' => -1, 'Q' => -1,
    'T' => -1, 'V' => -1, 'W' => -1, 'Z' => -1,
)

# Verify balance: 9(+1) + 8(0) + 9(-1) = 0
@assert sum(values(WORLDS_26)) == 0 "GF(3) balance violated"

# ══════════════════════════════════════════════════════════════════════════════
# Thread Structure
# ══════════════════════════════════════════════════════════════════════════════

struct Thread
    id::String
    title::Union{String, Nothing}
    created::Int64
    msg_count::Int
    trit::Int8
end

# ══════════════════════════════════════════════════════════════════════════════
# Decomposition Bag (One per World)
# ══════════════════════════════════════════════════════════════════════════════

struct WorldBag
    letter::Char
    trit::Int8
    threads::Vector{Thread}
    
    # Sheaf section: summary statistics
    total_messages::Int
    thread_count::Int
    dominant_theme::String
end

# ══════════════════════════════════════════════════════════════════════════════
# Adhesion (Connection between worlds)
# ══════════════════════════════════════════════════════════════════════════════

struct WorldAdhesion
    from::Char
    to::Char
    φ::Int8  # Transition morphism: trit(to) - trit(from) mod 3
    shared_concepts::Vector{String}  # Concepts appearing in both worlds
end

# ══════════════════════════════════════════════════════════════════════════════
# The 26-Decomposition
# ══════════════════════════════════════════════════════════════════════════════

struct Thread26Decomposition
    bags::Dict{Char, WorldBag}
    adhesions::Vector{WorldAdhesion}
    
    # Global section (sheaf consistency)
    total_threads::Int
    gf3_balanced::Bool
end

# ══════════════════════════════════════════════════════════════════════════════
# Assignment Function: Thread → World
# ══════════════════════════════════════════════════════════════════════════════

"""
Assign a thread to one of 26 worlds based on:
1. Thread trit determines world trit class
2. Thread ID hash determines specific world within class
"""
function assign_world(thread::Thread, seed::UInt64=0x42D)::Char
    # Get candidate worlds matching thread's trit
    candidates = [w for (w, t) in WORLDS_26 if t == thread.trit]
    
    if isempty(candidates)
        # Fallback: ERGODIC worlds accept any trit
        candidates = [w for (w, t) in WORLDS_26 if t == 0]
    end
    
    # Deterministic selection based on thread ID
    id_hash = hash(thread.id, seed)
    idx = (id_hash % length(candidates)) + 1
    
    candidates[idx]
end

# ══════════════════════════════════════════════════════════════════════════════
# Theme Extraction (simplified - production would use embeddings)
# ══════════════════════════════════════════════════════════════════════════════

const THEME_KEYWORDS = Dict(
    "categorical" => ["category", "functor", "topos", "sheaf", "morphism", "acset"],
    "color" => ["gay", "color", "hue", "trit", "splitmix", "rgb"],
    "distributed" => ["world", "goblin", "captp", "p2p", "nats", "distributed"],
    "synthesis" => ["create", "generate", "build", "implement", "fork"],
    "analysis" => ["verify", "check", "analyze", "validate", "constraint"],
    "coordination" => ["coordinate", "route", "balance", "orchestrate", "ergodic"],
    "music" => ["music", "audio", "synth", "sound", "opn", "aphex"],
    "proofs" => ["proof", "theorem", "lean", "narya", "formalize", "verify"],
)

function extract_theme(threads::Vector{Thread})::String
    if isempty(threads)
        return "empty"
    end
    
    # Count keyword matches across all titles
    counts = Dict{String, Int}()
    for (theme, keywords) in THEME_KEYWORDS
        counts[theme] = 0
        for t in threads
            title = something(t.title, "")
            for kw in keywords
                if occursin(lowercase(kw), lowercase(title))
                    counts[theme] += 1
                end
            end
        end
    end
    
    # Return dominant theme
    if all(v == 0 for v in values(counts))
        return "general"
    end
    
    argmax(counts)
end

# ══════════════════════════════════════════════════════════════════════════════
# Build the Decomposition
# ══════════════════════════════════════════════════════════════════════════════

function build_decomposition(threads::Vector{Thread}, seed::UInt64=0x42D)::Thread26Decomposition
    # Initialize bags
    world_threads = Dict{Char, Vector{Thread}}()
    for letter in 'A':'Z'
        world_threads[letter] = Thread[]
    end
    
    # Assign threads to worlds
    for thread in threads
        world = assign_world(thread, seed)
        push!(world_threads[world], thread)
    end
    
    # Create bags with sheaf sections
    bags = Dict{Char, WorldBag}()
    for letter in 'A':'Z'
        ts = world_threads[letter]
        bags[letter] = WorldBag(
            letter,
            WORLDS_26[letter],
            ts,
            sum(t.msg_count for t in ts; init=0),
            length(ts),
            extract_theme(ts)
        )
    end
    
    # Create adhesions (complete graph on 26 vertices = 325 edges)
    adhesions = WorldAdhesion[]
    for w1 in 'A':'Z'
        for w2 in (w1+1):'Z'
            φ = mod(WORLDS_26[w2] - WORLDS_26[w1] + 1, 3) - 1
            
            # Find shared concepts (simplified: shared keywords in titles)
            shared = String[]
            titles1 = [something(t.title, "") for t in bags[w1].threads]
            titles2 = [something(t.title, "") for t in bags[w2].threads]
            
            for (theme, _) in THEME_KEYWORDS
                if any(occursin(theme, lowercase(t)) for t in titles1) &&
                   any(occursin(theme, lowercase(t)) for t in titles2)
                    push!(shared, theme)
                end
            end
            
            push!(adhesions, WorldAdhesion(w1, w2, Int8(φ), shared))
        end
    end
    
    # Verify GF(3) balance
    total_trit = sum(bags[w].trit * bags[w].thread_count for w in 'A':'Z')
    gf3_balanced = mod(total_trit, 3) == 0
    
    Thread26Decomposition(
        bags,
        adhesions,
        length(threads),
        gf3_balanced
    )
end

# ══════════════════════════════════════════════════════════════════════════════
# Export to Markdown
# ══════════════════════════════════════════════════════════════════════════════

function to_markdown(decomp::Thread26Decomposition)::String
    lines = String[]
    
    push!(lines, "# Thread 26-Decomposition")
    push!(lines, "")
    push!(lines, "> Distillation of $(decomp.total_threads) threads into 26 worlds")
    push!(lines, "> GF(3) Balanced: $(decomp.gf3_balanced ? "✓" : "✗")")
    push!(lines, "")
    
    # Summary table
    push!(lines, "## World Summary")
    push!(lines, "")
    push!(lines, "| World | Trit | Threads | Messages | Theme |")
    push!(lines, "|-------|------|---------|----------|-------|")
    
    for letter in 'A':'Z'
        bag = decomp.bags[letter]
        trit_str = bag.trit == 1 ? "+1" : bag.trit == -1 ? "-1" : "0"
        push!(lines, "| $(letter) | $(trit_str) | $(bag.thread_count) | $(bag.total_messages) | $(bag.dominant_theme) |")
    end
    
    push!(lines, "")
    
    # Per-world details
    push!(lines, "## World Details")
    push!(lines, "")
    
    for letter in 'A':'Z'
        bag = decomp.bags[letter]
        trit_str = bag.trit == 1 ? "PLUS (+1)" : bag.trit == -1 ? "MINUS (-1)" : "ERGODIC (0)"
        
        push!(lines, "### World $(letter): $(trit_str)")
        push!(lines, "")
        push!(lines, "**Threads**: $(bag.thread_count) | **Messages**: $(bag.total_messages) | **Theme**: $(bag.dominant_theme)")
        push!(lines, "")
        
        # Top 5 threads by message count
        sorted = sort(bag.threads, by=t->t.msg_count, rev=true)
        top5 = sorted[1:min(5, length(sorted))]
        
        if !isempty(top5)
            push!(lines, "| Thread | Messages | Title |")
            push!(lines, "|--------|----------|-------|")
            for t in top5
                title = something(t.title, "(untitled)")
                title_short = length(title) > 50 ? title[1:47] * "..." : title
                push!(lines, "| $(t.id[1:16])... | $(t.msg_count) | $(title_short) |")
            end
            push!(lines, "")
        end
    end
    
    # Adhesion graph (simplified)
    push!(lines, "## Adhesion Structure")
    push!(lines, "")
    push!(lines, "```mermaid")
    push!(lines, "graph LR")
    
    # Show only adhesions with shared concepts
    for adh in decomp.adhesions
        if !isempty(adh.shared_concepts)
            φ_str = adh.φ == 1 ? "+1" : adh.φ == -1 ? "-1" : "0"
            push!(lines, "    $(adh.from) -->|φ=$(φ_str)| $(adh.to)")
        end
    end
    
    push!(lines, "```")
    push!(lines, "")
    
    join(lines, "\n")
end

# ══════════════════════════════════════════════════════════════════════════════
# Demo with sample threads
# ══════════════════════════════════════════════════════════════════════════════

function demo()
    # Sample threads (in production, load from JSONL)
    sample_threads = [
        Thread("T-019b13db-f777-71ee-924a-b42f68c6dcef", "JULES: Learnable Color + 3-MATCH", 1765564741495, 24, 0),
        Thread("T-9d0f4f78-57f6-47af-b759-63f61ba6c6a8", "Explore HIGHER CATEGORY & TOPOS thread", 1765198770550, 12, 1),
        Thread("T-019b57bc-01d3-72c8-afea-ed95db758d68", "PLUS (+1): Create ies symlink and index", 1766703497683, 4, 1),
        Thread("T-019b1193-4bd4-75f3-8faa-d7494a305833", "Continuing Gay.jl chromatic identity framework", 1765526424536, 108, 1),
        Thread("T-019b58a1-68da-736f-b0b9-e4c99a593e28", "Toad ACP flow analysis comparing Python asyncio", 1766718531803, 66, -1),
        Thread("T-019b3ea1-2fc6-70de-8718-07e2270f3c5d", "Document advanced music synthesis system architecture", 1766282309574, 48, 1),
        Thread("T-019b7953-c453-76e3-a0cc-8f22076e0ecb", "Extract transcript for 2-torial 7: Coalgebraic-modal extensions", 1767267091540, 12, -1),
        Thread("T-94d0e522-a2c0-462c-8bef-592db03fe078", "Custom abilities for self-interaction test scenarios", 1764839045864, 319, -1),
        Thread("T-019b4274-b674-754e-a853-86367a34c154", "Lazy directory trees with local cache in Hydra", 1766346503802, 160, 1),
        Thread("T-019b0342-1a7b-7373-b0c9-ddfe2af0e2cd", "Polarity bisimulation with partial total orders", 1765286222468, 275, -1),
    ]
    
    decomp = build_decomposition(sample_threads)
    println(to_markdown(decomp))
end

export Thread, Thread26Decomposition, build_decomposition, to_markdown, demo, WORLDS_26

end # module
