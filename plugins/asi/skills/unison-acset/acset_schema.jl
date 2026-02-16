# ACSet Schema for Unison Documentation Hierarchy
# Parses LLM text into structured attributed C-sets

module UnisonACSet

using ACSets

export UnisonDocSchema, build_unison_acset, trit_color

# GF(3) trit type
@enum Trit::Int8 MINUS=-1 ERGODIC=0 PLUS=1

# Hue to trit mapping
function hue_to_trit(h::Float64)::Trit
    h = mod(h, 360)
    if h < 60 || h >= 300
        PLUS
    elseif h < 180
        ERGODIC
    else
        MINUS
    end
end

# SplitMix64 for deterministic coloring
const GOLDEN = 0x9E3779B97F4A7C15
const MIX1 = 0xBF58476D1CE4E5B9
const MIX2 = 0x94D049BB133111EB

function splitmix64(seed::UInt64)::Tuple{UInt64, UInt64}
    seed = seed + GOLDEN
    z = seed
    z = (z ⊻ (z >> 30)) * MIX1
    z = (z ⊻ (z >> 27)) * MIX2
    (seed, z ⊻ (z >> 31))
end

function val_to_trit(val::UInt64)::Trit
    h = 360.0 * (val & 0xFFFF) / 65536.0
    hue_to_trit(h)
end

# ACSet Schema for Unison Docs
@present UnisonDocSchema(FreeSchema) begin
    # Objects (documentation nodes)
    Section::Ob
    Concept::Ob
    Ability::Ob
    Example::Ob
    Command::Ob
    
    # Morphisms (hierarchical relationships)
    section_concept::Hom(Concept, Section)    # concept belongs to section
    ability_requires::Hom(Ability, Ability)   # ability depends on ability
    example_concept::Hom(Example, Concept)    # example illustrates concept
    command_concept::Hom(Command, Concept)    # command implements concept
    
    # Attributes
    Title::AttrType
    Description::AttrType
    Code::AttrType
    Effect::AttrType
    TritVal::AttrType
    
    section_title::Attr(Section, Title)
    section_trit::Attr(Section, TritVal)
    
    concept_name::Attr(Concept, Title)
    concept_desc::Attr(Concept, Description)
    concept_trit::Attr(Concept, TritVal)
    
    ability_name::Attr(Ability, Title)
    ability_effect::Attr(Ability, Effect)
    ability_handler::Attr(Ability, Title)
    ability_trit::Attr(Ability, TritVal)
    
    example_code::Attr(Example, Code)
    example_trit::Attr(Example, TritVal)
    
    command_syntax::Attr(Command, Code)
    command_purpose::Attr(Command, Description)
    command_trit::Attr(Command, TritVal)
end

# Create typed ACSet
@acset_type UnisonDocs(UnisonDocSchema, 
    index=[:section_concept, :ability_requires, :example_concept, :command_concept])

# Build Unison ACSet from parsed documentation
function build_unison_acset(seed::UInt64=0x42D)  # 1069 = 0x42D (zubuyul)
    docs = UnisonDocs{String, String, String, String, Int8}()
    
    # Core sections with deterministic coloring
    sections = [
        ("Core Philosophy", 0),
        ("Language Constructs", 0),
        ("Abilities", 1),
        ("UCM Commands", -1),
        ("Distributed Computing", 1),
        ("Concurrency", 0),
    ]
    
    current_seed = seed
    section_ids = Dict{String, Int}()
    
    for (title, base_trit) in sections
        current_seed, val = splitmix64(current_seed)
        derived_trit = Int8(val_to_trit(val))
        # Blend base with derived for stability
        final_trit = (base_trit + derived_trit) ÷ 2
        
        id = add_part!(docs, :Section, 
            section_title=title, 
            section_trit=Int8(final_trit))
        section_ids[title] = id
    end
    
    # Concepts per section
    concepts = [
        ("Core Philosophy", [
            ("content-addressed", "Code identified by 512-bit SHA3 hash"),
            ("immutability", "Definitions never change once hashed"),
            ("hash-based-deps", "Dependencies pinned by hash, not version"),
        ]),
        ("Abilities", [
            ("IO", "File, network, console operations"),
            ("Exception", "Raise and catch errors"),
            ("Random", "Pseudo-random number generation"),
            ("Abort", "Early termination of computation"),
            ("Remote", "Distributed computation across nodes"),
            ("STM", "Software transactional memory"),
        ]),
        ("UCM Commands", [
            ("update", "Add typechecked code to codebase"),
            ("run", "Execute delayed computation"),
            ("compile", "Generate standalone binary"),
            ("lib.install", "Pull library from Unison Share"),
            ("move.term", "Instant refactoring via hash"),
        ]),
    ]
    
    for (section_name, concept_list) in concepts
        section_id = get(section_ids, section_name, 1)
        for (name, desc) in concept_list
            current_seed, val = splitmix64(current_seed)
            trit = Int8(val_to_trit(val))
            add_part!(docs, :Concept,
                section_concept=section_id,
                concept_name=name,
                concept_desc=desc,
                concept_trit=trit)
        end
    end
    
    # Abilities with handler info
    abilities = [
        ("IO", "Runtime effects", "Runtime"),
        ("Exception", "Error propagation", "catch/toEither"),
        ("Random", "PRNG", "splitmix seed"),
        ("Abort", "Halt execution", "toOptional!"),
        ("Remote", "Distributed compute", "Cloud runtime"),
        ("STM", "Atomic transactions", "STM.atomically"),
    ]
    
    ability_ids = Dict{String, Int}()
    for (name, effect, handler) in abilities
        current_seed, val = splitmix64(current_seed)
        trit = Int8(val_to_trit(val))
        id = add_part!(docs, :Ability,
            ability_name=name,
            ability_effect=effect,
            ability_handler=handler,
            ability_trit=trit)
        ability_ids[name] = id
    end
    
    # Ability dependencies
    set_subpart!(docs, ability_ids["Random"], :ability_requires, ability_ids["IO"])
    set_subpart!(docs, ability_ids["Remote"], :ability_requires, ability_ids["IO"])
    
    docs
end

# Verify GF(3) conservation
function verify_gf3(docs::UnisonDocs)
    section_trits = docs[:section_trit]
    concept_trits = docs[:concept_trit]
    ability_trits = docs[:ability_trit]
    
    all_trits = vcat(section_trits, concept_trits, ability_trits)
    total = sum(all_trits)
    
    (
        sum=total,
        mod3=mod(total, 3),
        conserved=mod(total, 3) == 0,
        distribution=(
            plus=count(==(1), all_trits),
            ergodic=count(==(0), all_trits),
            minus=count(==(-1), all_trits),
        )
    )
end

# Color representation
function trit_color(trit::Int8)::String
    if trit == 1
        "🔴 PLUS"
    elseif trit == 0
        "🟢 ERGODIC"
    else
        "🔵 MINUS"
    end
end

# Demo
function demo()
    println("Building Unison ACSet from seed 1069 (zubuyul)...")
    docs = build_unison_acset(UInt64(1069))
    
    println("\nSections:")
    for i in 1:nparts(docs, :Section)
        title = docs[i, :section_title]
        trit = docs[i, :section_trit]
        println("  $(trit_color(trit)) $title")
    end
    
    println("\nAbilities:")
    for i in 1:nparts(docs, :Ability)
        name = docs[i, :ability_name]
        handler = docs[i, :ability_handler]
        trit = docs[i, :ability_trit]
        println("  $(trit_color(trit)) $name → $handler")
    end
    
    gf3 = verify_gf3(docs)
    println("\nGF(3) Conservation:")
    println("  Sum: $(gf3.sum), Mod 3: $(gf3.mod3)")
    println("  Conserved: $(gf3.conserved ? "✓ YES" : "✗ NO")")
    println("  Distribution: +$(gf3.distribution.plus) ○$(gf3.distribution.ergodic) -$(gf3.distribution.minus)")
    
    docs
end

end # module
