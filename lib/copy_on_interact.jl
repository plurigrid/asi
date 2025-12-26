"""
Copy-on-Interact: Bidirectional sync between local ACSets and GitHub repos.

When a thread references another thread → create bidirectional link.
GitHub issues/PRs/mentions as interaction events.
Color interactions by relationship type using Gay.jl determinism.
"""

module CopyOnInteract

using ACSets
using Catlab.Present
using Catlab.CategoricalAlgebra

@present SchInteractiveACSet(FreeSchema) begin
    # Core objects
    Thread::Ob
    Skill::Ob
    Agent::Ob
    RemoteRef::Ob
    Interaction::Ob
    
    # Thread morphisms
    references::Hom(Thread, Thread)        # Thread → Thread citations
    attachment::Hom(Skill, Thread)         # Skill attached to thread
    participant::Hom(Agent, Thread)        # Agent in thread
    
    # Remote sync
    remote_source::Hom(RemoteRef, Thread)  # Remote → local mapping
    
    # Interaction log
    source_interaction::Hom(Interaction, Thread)
    target_interaction::Hom(Interaction, Thread)
    triggered_by::Hom(Interaction, Agent)
    involves_remote::Hom(Interaction, RemoteRef)
    
    # GitHub specific
    InteractionType::AttrType  # :fork, :pr, :issue, :mention, :star
    Color::AttrType            # OkLCH from Gay.jl
    Trit::AttrType             # GF(3): -1, 0, +1
    Timestamp::AttrType
    URL::AttrType
    Seed::AttrType
    
    interaction_type::Attr(Interaction, InteractionType)
    color::Attr(Interaction, Color)
    trit::Attr(Interaction, Trit)
    timestamp::Attr(Interaction, Timestamp)
    
    remote_url::Attr(RemoteRef, URL)
    remote_seed::Attr(RemoteRef, Seed)
    
    thread_seed::Attr(Thread, Seed)
    skill_name::Attr(Skill, AttrType)
    agent_id::Attr(Agent, AttrType)
end

@acset_type InteractiveACSets(SchInteractiveACSet)

# Interaction type → (Trit, Hue) mapping
const INTERACTION_SEMANTICS = Dict(
    :fork    => (trit=-1, hue=270.0),   # Purple: constraint/derivation
    :pr      => (trit=+1, hue=60.0),    # Orange: generation/contribution  
    :issue   => (trit=0,  hue=180.0),   # Cyan: coordination
    :mention => (trit=0,  hue=200.0),   # Blue-cyan: coordination
    :star    => (trit=+1, hue=45.0),    # Gold: appreciation/generation
    :review  => (trit=-1, hue=290.0),   # Purple: constraint/validation
)

struct RemoteRef
    url::String
    repo::String
    ref_type::Symbol  # :issue, :pr, :commit, :discussion
    number::Union{Int, Nothing}
    fetched::Bool
    last_sync::Float64
end

struct CopyOnInteractState
    local_state::InteractiveACSets
    remote_refs::Dict{String, RemoteRef}
    interaction_log::Vector{NamedTuple}
    seed::UInt64
    invocation_count::Int
end

function create_state(seed::UInt64=0x42D)
    CopyOnInteractState(
        InteractiveACSets(),
        Dict{String, RemoteRef}(),
        Vector{NamedTuple}(),
        seed,
        0
    )
end

# SplitMix64 for deterministic coloring
function splitmix64(seed::UInt64)
    z = seed + 0x9E3779B97F4A7C15
    z = (z ⊻ (z >> 30)) * 0xBF58476D1CE4E5B9
    z = (z ⊻ (z >> 27)) * 0x94D049BB133111EB
    z ⊻ (z >> 31)
end

function color_at(seed::UInt64, index::Int)
    state = seed
    for _ in 1:index
        state = splitmix64(state)
    end
    
    hue = (state % 360)
    L = 0.50 + (((state >> 8) % 100) / 500.0)
    C = 0.12 + (((state >> 16) % 100) / 500.0)
    
    (L=L, C=C, h=Float64(hue))
end

function on_interact!(state::CopyOnInteractState, ref_url::String, interaction_type::Symbol)
    """
    Triggered on any cross-boundary access.
    Fetches remote, merges, colors with Gay determinism.
    """
    
    # Parse GitHub URL
    parsed = parse_github_url(ref_url)
    isnothing(parsed) && return nothing
    
    # Check if already cached
    if haskey(state.remote_refs, ref_url) && state.remote_refs[ref_url].fetched
        cached = state.remote_refs[ref_url]
        if time() - cached.last_sync < 300.0  # 5 min cache
            return materialize_cached(state, cached, interaction_type)
        end
    end
    
    # Fetch and materialize
    remote = fetch_github_ref(parsed)
    isnothing(remote) && return nothing
    
    state.remote_refs[ref_url] = remote
    
    # Create interaction record
    interaction_id = log_interaction!(state, ref_url, interaction_type)
    
    # Merge into local ACSet
    merge_remote!(state, remote)
    
    interaction_id
end

function parse_github_url(url::String)
    patterns = [
        r"github\.com/([^/]+)/([^/]+)/issues/(\d+)" => :issue,
        r"github\.com/([^/]+)/([^/]+)/pull/(\d+)" => :pr,
        r"github\.com/([^/]+)/([^/]+)/commit/([a-f0-9]+)" => :commit,
        r"github\.com/([^/]+)/([^/]+)$" => :repo,
    ]
    
    for (pattern, ref_type) in patterns
        m = match(pattern, url)
        if !isnothing(m)
            return (
                owner = m.captures[1],
                repo = m.captures[2],
                number = length(m.captures) >= 3 ? tryparse(Int, m.captures[3]) : nothing,
                ref_type = ref_type
            )
        end
    end
    nothing
end

function log_interaction!(state::CopyOnInteractState, url::String, itype::Symbol)
    state.invocation_count += 1
    
    sem = get(INTERACTION_SEMANTICS, itype, (trit=0, hue=180.0))
    color = color_at(state.seed, state.invocation_count)
    
    # Override hue based on interaction type
    colored = (L=color.L, C=color.C, h=sem.hue)
    
    interaction = (
        id = state.invocation_count,
        url = url,
        type = itype,
        trit = sem.trit,
        color = colored,
        timestamp = time(),
    )
    
    push!(state.interaction_log, interaction)
    
    # Add to ACSet
    add_part!(state.local_state, :Interaction;
        interaction_type = itype,
        trit = sem.trit,
        color = colored,
        timestamp = time()
    )
    
    interaction
end

function merge_remote!(state::CopyOnInteractState, remote::RemoteRef)
    """
    DPO-style merge: find overlap, compute pushout
    """
    remote_id = add_part!(state.local_state, :RemoteRef;
        remote_url = remote.url,
        remote_seed = hash(remote.url)
    )
    
    remote_id
end

function create_bidirectional_link!(state::CopyOnInteractState, 
                                     thread_a::Int, thread_b::Int,
                                     link_type::Symbol=:references)
    """
    When thread A references thread B, create bidirectional link.
    """
    add_part!(state.local_state, :Thread)  # Ensure threads exist
    
    # Forward link
    set_subpart!(state.local_state, thread_a, :references, thread_b)
    
    # Log the interaction
    log_interaction!(state, "local:thread:$thread_a→$thread_b", link_type)
end

function verify_gf3_conservation(state::CopyOnInteractState)
    """
    Verify GF(3) conservation: sum of all trits ≡ 0 (mod 3)
    """
    total = sum(i.trit for i in state.interaction_log; init=0)
    mod(total, 3) == 0
end

function interaction_summary(state::CopyOnInteractState)
    by_type = Dict{Symbol, Vector}()
    for i in state.interaction_log
        if !haskey(by_type, i.type)
            by_type[i.type] = []
        end
        push!(by_type[i.type], i)
    end
    
    (
        total = length(state.interaction_log),
        by_type = Dict(k => length(v) for (k,v) in by_type),
        gf3_sum = sum(i.trit for i in state.interaction_log; init=0),
        gf3_conserved = verify_gf3_conservation(state),
        seed = state.seed,
    )
end

# Cobordism detection between remote refs
function find_cobordisms(state::CopyOnInteractState)
    """
    Find shared boundaries between different repo communities.
    A cobordism exists when two repos share contributors/interactions.
    """
    repos = unique([r.repo for r in values(state.remote_refs)])
    
    cobordisms = []
    for i in 1:length(repos)
        for j in (i+1):length(repos)
            shared = find_shared_interactions(state, repos[i], repos[j])
            if !isempty(shared)
                push!(cobordisms, (
                    repos = (repos[i], repos[j]),
                    shared = shared,
                    strength = length(shared),
                    trit = mod(sum(s.trit for s in shared), 3) - 1
                ))
            end
        end
    end
    
    cobordisms
end

function find_shared_interactions(state::CopyOnInteractState, repo_a::String, repo_b::String)
    # Find interactions that touch both repos
    filter(state.interaction_log) do i
        contains(i.url, repo_a) || contains(i.url, repo_b)
    end
end

# Export schema for external tools
function export_schema_json()
    Dict(
        "objects" => ["Thread", "Skill", "Agent", "RemoteRef", "Interaction"],
        "morphisms" => Dict(
            "references" => ["Thread", "Thread"],
            "attachment" => ["Skill", "Thread"],
            "participant" => ["Agent", "Thread"],
            "remote_source" => ["RemoteRef", "Thread"],
            "source_interaction" => ["Interaction", "Thread"],
            "target_interaction" => ["Interaction", "Thread"],
            "triggered_by" => ["Interaction", "Agent"],
            "involves_remote" => ["Interaction", "RemoteRef"],
        ),
        "attributes" => Dict(
            "Interaction" => ["type", "color", "trit", "timestamp"],
            "RemoteRef" => ["url", "seed"],
            "Thread" => ["seed"],
        ),
        "interaction_types" => collect(keys(INTERACTION_SEMANTICS)),
    )
end

end # module
