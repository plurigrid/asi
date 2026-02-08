"""
Reaction Network Construction

Implements chemical reaction networks with stoichiometric matrices,
mass-action kinetics, and organizational structure analysis.
"""

module ReactionNetworkModule

export ReactionNetwork, add_species!, add_reaction!
export stoichiometric_matrix, reaction_rate, compute_flux

using LinearAlgebra
using SparseArrays

"""
Chemical Reaction: reactants -> products with rate constant
"""
struct Reaction
    reactants::Dict{Symbol, Int}  # species -> stoichiometric coefficient
    products::Dict{Symbol, Int}
    rate_constant::Float64
    reversible::Bool

    function Reaction(reactants::Dict{Symbol, Int}, products::Dict{Symbol, Int},
                     rate_constant::Float64; reversible::Bool=false)
        new(reactants, products, rate_constant, reversible)
    end
end

"""
Reaction Network: collection of species and reactions
"""
mutable struct ReactionNetwork
    species::Vector{Symbol}
    reactions::Vector{Reaction}

    # Species index mapping
    species_index::Dict{Symbol, Int}

    function ReactionNetwork()
        new(Symbol[], Reaction[], Dict{Symbol, Int}())
    end
end

"""
Add species to network
"""
function add_species!(network::ReactionNetwork, species::Vector{Symbol})
    for s in species
        if !(s in network.species)
            push!(network.species, s)
            network.species_index[s] = length(network.species)
        end
    end
    return network
end

function add_species!(network::ReactionNetwork, species::Symbol)
    add_species!(network, [species])
end

"""
Add reaction to network

Example: add_reaction!(net, [:A, :B] => [:C], rate=0.1)
"""
function add_reaction!(network::ReactionNetwork, reaction_pair::Pair, rate::Float64; reversible::Bool=false)
    reactants_list, products_list = reaction_pair

    # Convert to dictionaries with stoichiometry
    reactants = Dict{Symbol, Int}()
    for r in reactants_list
        reactants[r] = get(reactants, r, 0) + 1
    end

    products = Dict{Symbol, Int}()
    for p in products_list
        products[p] = get(products, p, 0) + 1
    end

    # Ensure all species are registered
    all_species = unique(vcat(reactants_list, products_list))
    add_species!(network, all_species)

    # Create reaction
    rxn = Reaction(reactants, products, rate; reversible=reversible)
    push!(network.reactions, rxn)

    # Add reverse reaction if reversible
    if reversible
        reverse_rxn = Reaction(products, reactants, rate * 0.1; reversible=false)  # Assume equilibrium constant
        push!(network.reactions, reverse_rxn)
    end

    return network
end

"""
Compute stoichiometric matrix S

S[i,j] = net change in species i from reaction j
"""
function stoichiometric_matrix(network::ReactionNetwork)
    n_species = length(network.species)
    n_reactions = length(network.reactions)

    S = zeros(Int, n_species, n_reactions)

    for (j, rxn) in enumerate(network.reactions)
        # Products: positive coefficients
        for (species, coeff) in rxn.products
            i = network.species_index[species]
            S[i, j] += coeff
        end

        # Reactants: negative coefficients
        for (species, coeff) in rxn.reactants
            i = network.species_index[species]
            S[i, j] -= coeff
        end
    end

    return S
end

"""
Compute reaction rate for given concentrations (mass-action kinetics)
"""
function reaction_rate(rxn::Reaction, concentrations::Dict{Symbol, Float64})
    # Rate = k * ∏ [reactant]^stoichiometry
    rate = rxn.rate_constant

    for (species, coeff) in rxn.reactants
        conc = get(concentrations, species, 0.0)
        rate *= conc^coeff
    end

    return rate
end

"""
Compute flux vector for all reactions
"""
function compute_flux(network::ReactionNetwork, concentrations::Dict{Symbol, Float64})
    n_reactions = length(network.reactions)
    flux = zeros(n_reactions)

    for (j, rxn) in enumerate(network.reactions)
        flux[j] = reaction_rate(rxn, concentrations)
    end

    return flux
end

"""
Compute time derivatives: dc/dt = S * v(c)
"""
function compute_derivatives(network::ReactionNetwork, concentrations::Dict{Symbol, Float64})
    S = stoichiometric_matrix(network)
    v = compute_flux(network, concentrations)

    # Convert dict to vector
    c = [get(concentrations, species, 0.0) for species in network.species]

    # dc/dt = S * v
    dc_dt = S * v

    # Convert back to dict
    derivatives = Dict(network.species[i] => dc_dt[i] for i in 1:length(network.species))

    return derivatives
end

"""
Integrate reaction network using Euler method
"""
function integrate_ode(network::ReactionNetwork, initial_concentrations::Dict{Symbol, Float64},
                      time_span::Tuple{Float64, Float64}, dt::Float64=0.01)
    t_start, t_end = time_span
    n_steps = Int(ceil((t_end - t_start) / dt))

    # Initialize
    c = copy(initial_concentrations)
    trajectory = [copy(c)]
    times = [t_start]

    # Euler integration
    for step in 1:n_steps
        dc_dt = compute_derivatives(network, c)

        # Update concentrations
        for species in network.species
            c[species] = max(0.0, c[species] + dt * dc_dt[species])
        end

        push!(trajectory, copy(c))
        push!(times, t_start + step * dt)
    end

    return (times=times, trajectory=trajectory)
end

end  # module
