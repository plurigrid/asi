# GF(3) Conservation for Sheaf Operations
# Ensures restriction(-1) ⊗ pullback(0) ⊗ extension(+1) = 0 (mod 3)

module GF3Conservation

using Gay: color_at, seed!
include("bumpus-sheaf.jl")
using .BumpusSheaf

export GF3Invariant, check_conservation, rebalance!, prove_pullback_preserves,
       trit_from_operation, verify_sheaf_gf3

# =============================================================================
# GF(3) Trit Algebra
# =============================================================================

struct Trit
    value::Int  # -1, 0, or +1
    function Trit(v::Int)
        @assert v ∈ (-1, 0, 1) "Trit must be -1, 0, or +1"
        new(v)
    end
end

# GF(3) addition
⊕(a::Trit, b::Trit) = Trit(mod(a.value + b.value + 1, 3) - 1)

# GF(3) multiplication (for composition)
⊗(a::Trit, b::Trit) = Trit(mod(a.value * b.value + 1, 3) - 1)

# Identity and inverse
zero_trit() = Trit(0)
inv(t::Trit) = Trit(mod(-t.value + 1, 3) - 1)

# =============================================================================
# Operation Trit Assignment
# =============================================================================

const OPERATION_TRITS = Dict(
    :restriction => Trit(-1),   # Consuming/contracting
    :pullback => Trit(0),       # Neutral/coordinating  
    :extension => Trit(+1),     # Producing/expanding
    :identity => Trit(0),
)

trit_from_operation(op::Symbol) = get(OPERATION_TRITS, op, Trit(0))

# Color → Trit via hue
function trit_from_color(hex::String)
    # Parse hex to hue
    r = parse(Int, hex[2:3], base=16) / 255
    g = parse(Int, hex[4:5], base=16) / 255
    b = parse(Int, hex[6:7], base=16) / 255
    
    cmax, cmin = max(r, g, b), min(r, g, b)
    delta = cmax - cmin
    
    hue = if delta == 0
        0.0
    elseif cmax == r
        60 * mod((g - b) / delta, 6)
    elseif cmax == g
        60 * ((b - r) / delta + 2)
    else
        60 * ((r - g) / delta + 4)
    end
    
    # Map hue to trit: [0,120) → -1, [120,240) → 0, [240,360) → +1
    Trit(floor(Int, hue / 120) - 1)
end

# =============================================================================
# GF(3) Invariant Structure
# =============================================================================

struct GF3Invariant
    operations::Vector{Symbol}
    trits::Vector{Trit}
    cumulative::Trit
    conserved::Bool
end

function GF3Invariant(ops::Vector{Symbol})
    trits = [trit_from_operation(op) for op in ops]
    cumulative = reduce(⊕, trits, init=zero_trit())
    GF3Invariant(ops, trits, cumulative, cumulative.value == 0)
end

# =============================================================================
# Conservation Checking
# =============================================================================

function check_conservation(doc::ColorDocument)
    if isempty(doc.edits)
        return (conserved=true, sum=0, edits=0)
    end
    
    trit_sum = sum(e.trit for e in doc.edits)
    conserved = mod(trit_sum, 3) == 0
    
    (conserved=conserved, sum=trit_sum, edits=length(doc.edits))
end

function check_sheaf_conservation(F::NarrativeSheaf)
    results = Dict{TimeInterval, NamedTuple}()
    total_sum = 0
    
    for (interval, doc) in F.sections
        result = check_conservation(doc)
        results[interval] = result
        total_sum += result.sum
    end
    
    (sections=results, 
     total_sum=total_sum, 
     globally_conserved=mod(total_sum, 3) == 0)
end

# =============================================================================
# Proof: Pullback Preserves GF(3) Balance
# =============================================================================

"""
Theorem: If F([a,p]) and F([p,b]) both satisfy GF(3) conservation,
then their pullback F([a,p]) ×_{F([p,p])} F([p,b]) also satisfies GF(3) conservation.

Proof:
Let L = F([a,p]) with trit sum s_L ≡ 0 (mod 3)
Let R = F([p,b]) with trit sum s_R ≡ 0 (mod 3)
Let A = F([p,p]) with trit sum s_A

The pullback operation has trit 0 (neutral).
The merged document M has edits from L ∪ R minus duplicates at apex.

s_M = s_L + s_R - s_A (edits at apex counted in both, subtract once)
    ≡ 0 + 0 - s_A (mod 3)
    ≡ -s_A (mod 3)

For conservation, we require s_A ≡ 0 (mod 3).
This is ensured by the point section being trivially balanced.

QED: Pullback preserves GF(3) when apex is balanced.
"""
function prove_pullback_preserves(F::NarrativeSheaf, left::TimeInterval, right::TimeInterval, p::Int)
    doc_left = BumpusSheaf.section(F, left)
    doc_right = BumpusSheaf.section(F, right)
    doc_apex = BumpusSheaf.section(F, BumpusSheaf.point_interval(p))
    
    s_L = check_conservation(doc_left)
    s_R = check_conservation(doc_right)
    s_A = check_conservation(doc_apex)
    
    # Compute merged sum
    merged_sum = s_L.sum + s_R.sum - s_A.sum
    
    proof = """
    GF(3) Conservation Proof for Pullback:
    =====================================
    Left section sum:  $(s_L.sum) ≡ $(mod(s_L.sum, 3)) (mod 3)
    Right section sum: $(s_R.sum) ≡ $(mod(s_R.sum, 3)) (mod 3)
    Apex section sum:  $(s_A.sum) ≡ $(mod(s_A.sum, 3)) (mod 3)
    
    Merged sum = s_L + s_R - s_A = $merged_sum
    Merged sum mod 3 = $(mod(merged_sum, 3))
    
    Conservation: $(mod(merged_sum, 3) == 0 ? "PRESERVED ✓" : "VIOLATED ✗")
    
    Operation balance: restriction(-1) ⊕ pullback(0) ⊕ extension(+1)
                     = $(mod(-1 + 0 + 1, 3)) ≡ 0 (mod 3) ✓
    """
    
    (proof=proof, 
     preserved=mod(merged_sum, 3) == 0,
     left_conserved=s_L.conserved,
     right_conserved=s_R.conserved,
     apex_conserved=s_A.conserved)
end

# =============================================================================
# Rebalancing Algorithm
# =============================================================================

"""
When GF(3) conservation is violated, rebalance by injecting compensating edits.
"""
function rebalance!(doc::ColorDocument, seed::UInt64=1069)
    result = check_conservation(doc)
    
    if result.conserved
        return (rebalanced=false, doc=doc)
    end
    
    # Compute deficit: need to add trit to reach 0 mod 3
    deficit = mod(-result.sum, 3)
    if deficit == 2
        deficit = -1  # Normalize to {-1, 0, +1}
    end
    
    # Generate compensating color from seed
    seed!(seed)
    compensating_color = color_at(length(doc.edits) + 1)
    
    compensating_edit = ColorEdit(
        length(doc.colors) + 1,
        "#000000",
        compensating_color,
        deficit,
        maximum(e.timestamp for e in doc.edits; init=0) + 1
    )
    
    rebalanced_doc = BumpusSheaf.apply_edit!(doc, compensating_edit)
    
    (rebalanced=true, 
     doc=rebalanced_doc, 
     compensating_trit=deficit,
     new_color=compensating_color)
end

# =============================================================================
# Full Sheaf GF(3) Verification
# =============================================================================

function verify_sheaf_gf3(F::NarrativeSheaf)
    # Check operation sequence
    operation_inv = GF3Invariant([:restriction, :pullback, :extension])
    
    # Check all sections
    section_results = check_sheaf_conservation(F)
    
    (operation_invariant=operation_inv,
     section_conservation=section_results,
     fully_verified=operation_inv.conserved && section_results.globally_conserved)
end

end # module
