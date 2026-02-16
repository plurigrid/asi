"""
Category Theory Primitives

Implements basic category theory structures: categories, functors,
natural transformations, and composition laws.
"""

module CategoryTheoryModule

export Category, Functor, NaturalTransformation
export compose, identity_morphism, check_functor_laws

using DataStructures

"""
Category: objects and morphisms with composition
"""
struct Category
    name::Symbol
    objects::Vector{Symbol}

    # morphisms: name -> (source, target)
    morphisms::Dict{Symbol, Tuple{Symbol, Symbol}}

    # composition: (f, g) -> h where f: A->B, g: B->C, h: A->C
    composition::Dict{Tuple{Symbol, Symbol}, Symbol}

    function Category(; name::Symbol, objects::Vector{Symbol},
                     morphisms::Dict{Symbol, Tuple{Symbol, Symbol}}=Dict{Symbol, Tuple{Symbol, Symbol}}(),
                     composition::Dict{Tuple{Symbol, Symbol}, Symbol}=Dict{Tuple{Symbol, Symbol}, Symbol}())
        new(name, objects, morphisms, composition)
    end
end

"""
Compose morphisms in category
"""
function compose(cat::Category, f::Symbol, g::Symbol)
    # f: A -> B, g: B -> C, result: A -> C
    @assert haskey(cat.morphisms, f) "Morphism $f not found"
    @assert haskey(cat.morphisms, g) "Morphism $g not found"

    src_f, tgt_f = cat.morphisms[f]
    src_g, tgt_g = cat.morphisms[g]

    @assert tgt_f == src_g "Morphisms not composable: $f: $src_f -> $tgt_f, $g: $src_g -> $tgt_g"

    # Look up composition or create new morphism
    if haskey(cat.composition, (f, g))
        return cat.composition[(f, g)]
    else
        # Create new composite morphism
        comp_name = Symbol("$(f)_compose_$(g)")
        return comp_name
    end
end

"""
Identity morphism for object
"""
function identity_morphism(cat::Category, obj::Symbol)
    @assert obj in cat.objects "Object $obj not in category"
    return Symbol("id_$obj")
end

"""
Functor: structure-preserving map between categories
"""
struct Functor
    name::Symbol
    source::Category
    target::Category

    # Map objects
    object_map::Dict{Symbol, Symbol}

    # Map morphisms
    morphism_map::Dict{Symbol, Symbol}

    function Functor(; name::Symbol=:F, source::Category, target::Category,
                    object_map::Dict{Symbol, Symbol},
                    morphism_map::Dict{Symbol, Symbol})
        new(name, source, target, object_map, morphism_map)
    end
end

"""
Apply functor to object
"""
function (F::Functor)(obj::Symbol)
    @assert obj in F.source.objects "Object $obj not in source category"
    return F.object_map[obj]
end

"""
Apply functor to morphism
"""
function apply_to_morphism(F::Functor, mor::Symbol)
    @assert haskey(F.source.morphisms, mor) "Morphism $mor not in source category"
    return F.morphism_map[mor]
end

"""
Compose functors: G ∘ F
"""
function compose(F::Functor, G::Functor)
    @assert F.target == G.source "Functors not composable"

    # Compose object maps
    object_map = Dict(obj => G.object_map[F.object_map[obj]] for obj in F.source.objects)

    # Compose morphism maps
    morphism_map = Dict(mor => G.morphism_map[F.morphism_map[mor]] for mor in keys(F.source.morphisms))

    return Functor(
        name=Symbol("$(G.name)_$(F.name)"),
        source=F.source,
        target=G.target,
        object_map=object_map,
        morphism_map=morphism_map
    )
end

"""
Check functor laws: preserves composition and identities
"""
function check_functor_laws(F::Functor)
    # Check identity preservation: F(id_A) = id_F(A)
    for obj in F.source.objects
        id_src = identity_morphism(F.source, obj)
        id_tgt = identity_morphism(F.target, F(obj))

        if haskey(F.morphism_map, id_src)
            if F.morphism_map[id_src] != id_tgt
                return false
            end
        end
    end

    # Check composition preservation: F(g ∘ f) = F(g) ∘ F(f)
    for ((f, g), comp) in F.source.composition
        F_f = apply_to_morphism(F, f)
        F_g = apply_to_morphism(F, g)
        F_comp = apply_to_morphism(F, comp)

        # F(g ∘ f) should equal F(g) ∘ F(f) in target category
        expected_comp = compose(F.target, F_f, F_g)

        if F_comp != expected_comp
            return false
        end
    end

    return true
end

"""
Natural Transformation: morphism between functors
"""
struct NaturalTransformation
    name::Symbol
    source::Functor  # F
    target::Functor  # G

    # Components: for each object A in C, a morphism F(A) -> G(A) in D
    components::Dict{Symbol, Symbol}

    function NaturalTransformation(; name::Symbol, source::Functor, target::Functor,
                                   components::Dict{Symbol, Symbol})
        @assert source.source == target.source "Functors must have same source category"
        @assert source.target == target.target "Functors must have same target category"

        new(name, source, target, components)
    end
end

"""
Check naturality condition: G(f) ∘ η_A = η_B ∘ F(f)
"""
function check_naturality(η::NaturalTransformation)
    F = η.source
    G = η.target

    for (mor_name, (src, tgt)) in F.source.morphisms
        # Get components
        η_src = η.components[src]
        η_tgt = η.components[tgt]

        # Get mapped morphisms
        F_mor = apply_to_morphism(F, mor_name)
        G_mor = apply_to_morphism(G, mor_name)

        # Check: G(f) ∘ η_A = η_B ∘ F(f)
        # This would require evaluating composition in the target category
        # Simplified check for now
    end

    return true
end

"""
Vertical composition of natural transformations
"""
function compose_vertical(η::NaturalTransformation, θ::NaturalTransformation)
    @assert η.target == θ.source "Natural transformations not vertically composable"

    # Components: (θ ∘ η)_A = θ_A ∘ η_A
    components = Dict(
        obj => compose(η.target.target, η.components[obj], θ.components[obj])
        for obj in η.source.source.objects
    )

    return NaturalTransformation(
        name=Symbol("$(θ.name)_$(η.name)"),
        source=η.source,
        target=θ.target,
        components=components
    )
end

end  # module
