#=
SkillCategory.jl - AlgebraicJulia Runtime for Categorical Skill Operations

This module provides runtime categorical operations using AlgebraicJulia's
ACSets and Catlab infrastructure.

Skills are objects in a category, bridges are morphisms.
Composition is associative, identities exist.
GF(3) is a functor from Skills to the group Z/3Z.
=#

module SkillCategory

using Catlab
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.Programs

# ============================================================================
# GF(3) TRIT STRUCTURE
# ============================================================================

"""GF(3) = Z/3Z, the cyclic group of order 3"""
struct GF3
    value::Int  # 0, 1, or 2
    
    function GF3(v::Int)
        new(mod(v, 3))
    end
end

# GF(3) arithmetic
Base.:+(a::GF3, b::GF3) = GF3(a.value + b.value)
Base.:-(a::GF3) = GF3(3 - a.value)
Base.:-(a::GF3, b::GF3) = a + (-b)
Base.:(==)(a::GF3, b::GF3) = a.value == b.value
Base.zero(::Type{GF3}) = GF3(0)
Base.one(::Type{GF3}) = GF3(1)

# Named constants
const PLUS = GF3(1)
const ERGODIC = GF3(0)
const MINUS = GF3(2)  # -1 ≡ 2 (mod 3)

"""Check if a list of trits is balanced (sums to 0)"""
isbalanced(trits::Vector{GF3}) = sum(t.value for t in trits) % 3 == 0

# ============================================================================
# SKILL SCHEMA (ACSET)
# ============================================================================

"""
Skill schema as an ACSet (Attributed C-Set).
Objects: Skill, Bridge, Port
Morphisms: source, target (for bridges), skill (for ports)
Attributes: name, trit, category
"""
@present SchSkill(FreeSchema) begin
    # Objects
    Skill::Ob
    Bridge::Ob
    Port::Ob
    
    # Morphisms
    source::Hom(Bridge, Skill)
    target::Hom(Bridge, Skill)
    owner::Hom(Port, Skill)
    
    # Attributes
    Name::AttrType
    Trit::AttrType
    Category::AttrType
    Direction::AttrType
    
    skill_name::Attr(Skill, Name)
    skill_trit::Attr(Skill, Trit)
    skill_category::Attr(Skill, Category)
    
    bridge_name::Attr(Bridge, Name)
    
    port_name::Attr(Port, Name)
    port_direction::Attr(Port, Direction)
end

"""The ACSet type for skill graphs"""
@acset_type SkillGraph(SchSkill, 
    index=[:source, :target, :owner])

# ============================================================================
# SKILL OPERATIONS
# ============================================================================

"""Create a new skill graph"""
function skill_graph()
    SkillGraph{String, Int, String, Symbol}()
end

"""Add a skill to the graph"""
function add_skill!(g::SkillGraph, name::String, trit::GF3, category::String)
    add_part!(g, :Skill, 
        skill_name=name, 
        skill_trit=trit.value, 
        skill_category=category)
end

"""Add a bridge between skills"""
function add_bridge!(g::SkillGraph, name::String, src_idx::Int, tgt_idx::Int)
    add_part!(g, :Bridge,
        bridge_name=name,
        source=src_idx,
        target=tgt_idx)
end

"""Add a port to a skill"""
function add_port!(g::SkillGraph, name::String, skill_idx::Int, direction::Symbol)
    add_part!(g, :Port,
        port_name=name,
        owner=skill_idx,
        port_direction=direction)
end

"""Get the trit of a skill by index"""
get_trit(g::SkillGraph, idx::Int) = GF3(g[idx, :skill_trit])

"""Check if the skill graph is GF(3) balanced"""
function isbalanced(g::SkillGraph)
    trits = [GF3(g[i, :skill_trit]) for i in parts(g, :Skill)]
    isbalanced(trits)
end

# ============================================================================
# POLYNOMIAL FUNCTORS
# ============================================================================

"""
A Polynomial Functor p: Set → Set
p(Y) = Σ (i : positions), (directions(i) → Y)
"""
struct Poly{P, D}
    positions::Vector{P}
    directions::Dict{P, Vector{D}}
end

"""The identity polynomial y"""
identity_poly() = Poly([:unit], Dict(:unit => [:unit]))

"""Polynomial composition (substitution): p ◃ q"""
function compose_poly(p::Poly{P1,D1}, q::Poly{P2,D2}) where {P1,D1,P2,D2}
    # New positions: pairs (i, f) where i ∈ p.positions and f: p.directions(i) → q.positions
    new_positions = []
    new_directions = Dict()
    
    for i in p.positions
        for f in Iterators.product(fill(q.positions, length(p.directions[i]))...)
            pos = (i, f)
            push!(new_positions, pos)
            # Directions at (i, f): pairs (a, b) where a ∈ p.directions(i), b ∈ q.directions(f(a))
            dirs = []
            for (idx, a) in enumerate(p.directions[i])
                q_pos = f[idx]
                for b in q.directions[q_pos]
                    push!(dirs, (a, b))
                end
            end
            new_directions[pos] = dirs
        end
    end
    
    Poly(new_positions, new_directions)
end

# ============================================================================
# SKILL AS POLYNOMIAL
# ============================================================================

"""A Skill with polynomial interface"""
struct PolySkill
    name::String
    trit::GF3
    poly::Poly
end

"""Create a skill polynomial from input/output ports"""
function skill_poly(name::String, trit::GF3, inputs::Vector{String}, outputs::Vector{String})
    # Positions = output types, Directions = input types
    positions = isempty(outputs) ? [:unit] : Symbol.(outputs)
    directions = Dict(p => isempty(inputs) ? [:unit] : Symbol.(inputs) for p in positions)
    PolySkill(name, trit, Poly(positions, directions))
end

"""Compose two skill polynomials"""
function compose_skills(s1::PolySkill, s2::PolySkill)
    PolySkill(
        "($(s1.name) ◃ $(s2.name))",
        s1.trit + s2.trit,
        compose_poly(s1.poly, s2.poly)
    )
end

# ============================================================================
# TRIADS
# ============================================================================

"""A balanced triad of skills"""
struct Triad
    s1::PolySkill
    s2::PolySkill
    s3::PolySkill
    
    function Triad(s1, s2, s3)
        @assert isbalanced([s1.trit, s2.trit, s3.trit]) "Triad must be GF(3) balanced"
        new(s1, s2, s3)
    end
end

"""Get the composite trit of a triad (always ERGODIC)"""
composite_trit(t::Triad) = t.s1.trit + t.s2.trit + t.s3.trit

# ============================================================================
# COALGEBRAS
# ============================================================================

"""
A Coalgebra for polynomial p is a state machine:
- state : Type
- observe : state → p.positions
- transition : (s : state) → p.directions(observe(s)) → state
"""
struct Coalgebra{S, P, D}
    poly::Poly{P, D}
    initial::S
    observe::Function   # S → P
    transition::Function  # (S, D) → S
end

"""Run a coalgebra for n steps"""
function run_coalgebra(c::Coalgebra, n::Int)
    trajectory = [(c.initial, c.observe(c.initial))]
    state = c.initial
    
    for _ in 1:n
        pos = c.observe(state)
        dirs = c.poly.directions[pos]
        if isempty(dirs)
            break
        end
        # Pick first available direction (deterministic)
        dir = first(dirs)
        state = c.transition(state, dir)
        push!(trajectory, (state, c.observe(state)))
    end
    
    trajectory
end

# ============================================================================
# WIRING DIAGRAMS
# ============================================================================

"""Create a wiring diagram for a triad"""
function triad_diagram(t::Triad)
    d = WiringDiagram([:input], [:output])
    
    # Add boxes for each skill
    b1 = add_box!(d, Box(Symbol(t.s1.name), [:in], [:out]))
    b2 = add_box!(d, Box(Symbol(t.s2.name), [:in], [:out]))
    b3 = add_box!(d, Box(Symbol(t.s3.name), [:in], [:out]))
    
    # Wire them sequentially
    add_wire!(d, (input_id(d), 1) => (b1, 1))
    add_wire!(d, (b1, 1) => (b2, 1))
    add_wire!(d, (b2, 1) => (b3, 1))
    add_wire!(d, (b3, 1) => (output_id(d), 1))
    
    d
end

# ============================================================================
# SHEAF GLUING (SIMPLIFIED)
# ============================================================================

"""
A presheaf over skill space assigns data to each "open" set of skills
"""
struct SkillPresheaf{T}
    sections::Dict{Set{String}, T}  # Open set → Section data
    
    function SkillPresheaf{T}() where T
        new(Dict{Set{String}, T}())
    end
end

"""Add a section over an open set"""
function add_section!(p::SkillPresheaf{T}, open_set::Set{String}, data::T) where T
    p.sections[open_set] = data
end

"""Check the gluing condition: sections agree on overlaps"""
function check_gluing(p::SkillPresheaf{T}, eq::Function) where T
    opens = collect(keys(p.sections))
    for i in 1:length(opens)
        for j in (i+1):length(opens)
            overlap = intersect(opens[i], opens[j])
            if !isempty(overlap)
                # Sections should agree on overlap
                s1 = p.sections[opens[i]]
                s2 = p.sections[opens[j]]
                if !eq(s1, s2, overlap)
                    return false
                end
            end
        end
    end
    true
end

# ============================================================================
# UNWORLD FEDERATION
# ============================================================================

"""Create the UNWORLD federation as a skill graph"""
function unworld_federation()
    g = skill_graph()
    
    # Add the three agents
    causality = add_skill!(g, "causality", PLUS, "federation")
    two_monad = add_skill!(g, "2-monad", ERGODIC, "federation")
    amp = add_skill!(g, "amp", MINUS, "federation")
    
    # Add bridges
    add_bridge!(g, "generate", causality, two_monad)
    add_bridge!(g, "coordinate", two_monad, amp)
    add_bridge!(g, "verify", amp, causality)  # Feedback loop
    
    @assert isbalanced(g) "UNWORLD federation must be balanced"
    
    g
end

"""Create UNWORLD as polynomial skills"""
function unworld_poly_skills()
    causality = skill_poly("causality", PLUS, ["seed"], ["generation"])
    two_monad = skill_poly("2-monad", ERGODIC, ["skills"], ["coordinated"])
    amp = skill_poly("amp", MINUS, ["proposal"], ["verified"])
    
    Triad(causality, two_monad, amp)
end

# ============================================================================
# EXPORTS
# ============================================================================

export GF3, PLUS, ERGODIC, MINUS, isbalanced
export SkillGraph, skill_graph, add_skill!, add_bridge!, add_port!, get_trit
export Poly, compose_poly, PolySkill, skill_poly, compose_skills
export Triad, composite_trit
export Coalgebra, run_coalgebra
export SkillPresheaf, add_section!, check_gluing
export triad_diagram
export unworld_federation, unworld_poly_skills

end # module
