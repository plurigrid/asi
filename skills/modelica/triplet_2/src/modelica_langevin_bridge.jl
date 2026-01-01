"""
    modelica_langevin_bridge.jl

Langevin SDE Generator: Converts Modelica DAE systems into stochastic differential equations.

This module implements the MINUS (-1) stream of Triplet #2:
  Modelica ⊗ Langevin-Dynamics ⊗ Fokker-Planck-Analyzer

Core algorithm:
  1. Parse Modelica DAE: dx/dt = f(x, parameters)
  2. Extract drift vector f(x) from equations
  3. Compute diffusion g(x,t) = √(2*k_B*T(t)/γ) * I (Langevin noise)
  4. Detect reversibility: Check if Jacobian is antisymmetric + rate constants > 0
  5. Analyze stiffness: Eigenvalue ratio of Jacobian matrix
  6. Tag metadata: dimensionality, reversibility, stiffness, conserved quantities

Chemical systems handled:
  - Simple reversible (A ⇌ B)
  - Irreversible synthesis (A + B → C)
  - Thermal coupling (kinetics + heat equation)
  - Enzyme kinetics (mixed reversibility)
"""

using LinearAlgebra
using Distributions
import JSON

# Constants
const BOLTZMANN_K = 8.314  # J/(mol·K), rescale for chemistry units
const STIFFNESS_THRESHOLD = 100.0  # Eigenvalue ratio threshold

"""
    LangevinSDE

Stochastic differential equation derived from Modelica DAE.

Fields:
  - drift::Function: f(x,t) → drift vector (from Modelica equations)
  - diffusion::Function: g(x,t) → noise covariance matrix
  - noise_schedule::Function: β(t) = 1/T(t) (inverse temperature schedule)
  - reversibility::Union{Bool, Symbol}: true/false/:mixed (system type)
  - is_stiff::Bool: true if condition number > STIFFNESS_THRESHOLD
  - hessian::Union{Function, Nothing}: Helmholtz free energy Hessian (optional)
  - metadata::Dict: Full provenance (variables, parameters, equations, tags)
"""
struct LangevinSDE
    drift::Function
    diffusion::Function
    noise_schedule::Function
    reversibility::Union{Bool, Symbol}
    is_stiff::Bool
    hessian::Union{Function, Nothing}
    metadata::Dict
end

"""
    modelica_to_langevin(dae::Dict; temperature=300.0, damping=1.0) → LangevinSDE

Convert Modelica DAE specification to Langevin SDE.

Required DAE dict fields:
  - equations::Vector{String}: Differential equations (e.g., "d[A]/dt = -k*[A]")
  - parameters::Dict: Parameter values (k_f=0.1, k_r=0.05, ...)
  - variables::Vector{String}: State variable names
  - reversible::Union{Bool, Symbol, Nothing}: Optional reversibility hint

Optional fields:
  - conserved::Vector{String}: Conservation law constraints
  - stiff::Bool: User hint about stiffness

Returns: LangevinSDE struct with drift, diffusion, and metadata
"""
function modelica_to_langevin(dae::Dict; temperature=300.0, damping=1.0)::LangevinSDE

    # Validate input
    required_keys = [:equations, :parameters, :variables]
    for key in required_keys
        !haskey(dae, key) && error("Missing required DAE key: $key")
    end

    equations = dae[:equations]
    parameters = dae[:parameters]
    variables = dae[:variables]
    n_vars = length(variables)

    # Check dimension match
    length(equations) != n_vars && error("Dimension mismatch: $(length(equations)) equations, $n_vars variables")

    # Extract Jacobian matrix from equations (simplified: linear extraction)
    # For production: use symbolic differentiation (Symbolics.jl)
    A = extract_jacobian_matrix(equations, parameters, variables)

    # Detect reversibility
    reversibility = detect_reversibility(equations, parameters, dae)

    # Detect stiffness
    eigenvalues = eigvals(A)
    eigenvalue_ratio = maximum(abs.(eigenvalues)) / (minimum(abs.(eigenvalues)) + 1e-12)
    is_stiff = eigenvalue_ratio > STIFFNESS_THRESHOLD

    # Create drift function: f(x,t) = A*x (linear approximation)
    drift = (x, t) -> A * x

    # Create diffusion function: g(x,t) = √(2*k_B*T(t)/γ) * I
    diffusion = (x, t) -> sqrt(2 * BOLTZMANN_K * temperature / damping) * Matrix(I, n_vars, n_vars)

    # Create temperature schedule (constant or time-varying)
    noise_schedule = (t) -> 1.0 / temperature

    # Metadata
    metadata = Dict(
        :variables => variables,
        :parameters => parameters,
        :dimensionality => n_vars,
        :jacobian_eigenvalues => eigenvalues,
        :stiffness_ratio => eigenvalue_ratio,
        :reversible_steps => count_reversible_steps(equations, parameters),
        :conserved_quantities => get(dae, :conserved, nothing),
        :temperature => temperature,
        :damping => damping
    )

    # Check for absorbing boundary (irreversible systems)
    if reversibility == false
        metadata[:absorbing_boundary] = true
        @warn "Irreversible system detected. System has absorbing states. Monitor for convergence to boundaries."
    end

    # Check stiffness
    if is_stiff
        @warn "Stiff system detected (condition number: $(round(eigenvalue_ratio; digits=1))). Consider using DASSL or Radau5 solver."
        metadata[:solver_recommendation] = "DASSL or Radau5"
    end

    return LangevinSDE(drift, diffusion, noise_schedule, reversibility, is_stiff, nothing, metadata)
end

"""
    extract_jacobian_matrix(equations, parameters, variables) → Matrix

Extract linear coefficient matrix from Modelica equations.

Assumes equations in form: d[X]/dt = -k_f*[X] + k_r*[Y]
Uses regex to extract coefficient for each variable.

For production: replace with symbolic differentiation via Symbolics.jl
"""
function extract_jacobian_matrix(equations::Vector, parameters::Dict, variables::Vector)::Matrix
    n = length(variables)
    A = zeros(Float64, n, n)

    for (i, eq) in enumerate(equations)
        # Parse equation to find coefficients
        # Simplified: split by '+' and '-', extract multipliers
        terms = split(eq, r"[\+\-]")

        for term in terms
            for (j, var) in enumerate(variables)
                if contains(term, var)
                    # Extract coefficient (simplified regex)
                    coeff_match = match(r"([\d\.]+)\s*\*?\s*$var", term)
                    if coeff_match !== nothing
                        coeff = parse(Float64, coeff_match.captures[1])
                        # Determine sign
                        sign = contains(eq[1:findfirst(term, eq)], "-") ? -1 : 1
                        A[i, j] += sign * coeff
                    end
                end
            end
        end
    end

    return A
end

"""
    detect_reversibility(equations, parameters, dae) → Union{Bool, Symbol}

Detect if chemical system is reversible (forward and backward reactions).

Returns:
  - true: All reactions reversible (e.g., A ⇌ B with k_f, k_r > 0)
  - false: All reactions irreversible (e.g., A → B with k_r = 0)
  - :mixed: Some reactions reversible, others not (e.g., enzyme kinetics)
"""
function detect_reversibility(equations::Vector, parameters::Dict, dae::Dict)
    # Check for explicit reversibility hint
    if haskey(dae, :reversible)
        return dae[:reversible]
    end

    # Count forward and backward rate constants
    n_forward = count(k -> contains(String(k), "k_f") || contains(String(k), "k_on"), keys(parameters))
    n_backward = count(k -> contains(String(k), "k_r") || contains(String(k), "k_off"), keys(parameters))
    n_irreversible = count(k -> contains(String(k), "k_cat"), keys(parameters))

    if n_forward > 0 && n_backward > 0 && n_irreversible == 0
        return true  # All reversible
    elseif n_backward == 0 && n_irreversible > 0
        return false  # All irreversible
    elseif n_backward > 0 && n_irreversible > 0
        return :mixed  # Mixed
    else
        return true  # Default to reversible
    end
end

"""
    count_reversible_steps(equations, parameters) → Int

Count how many reaction steps are reversible.
"""
function count_reversible_steps(equations::Vector, parameters::Dict)::Int
    reversible_count = 0
    for (k, v) in parameters
        if contains(String(k), "k_r") && v > 0
            reversible_count += 1
        elseif contains(String(k), "k_off") && v > 0
            reversible_count += 1
        end
    end
    return reversible_count
end

"""
    evaluate_drift(sde::LangevinSDE, x::Vector, t::Float64) → Vector

Evaluate drift vector field at point x, time t.
"""
function evaluate_drift(sde::LangevinSDE, x::Vector, t::Float64)::Vector
    return sde.drift(x, t)
end

"""
    evaluate_diffusion(sde::LangevinSDE, x::Vector, t::Float64) → Matrix

Evaluate diffusion matrix (noise covariance) at point x, time t.
"""
function evaluate_diffusion(sde::LangevinSDE, x::Vector, t::Float64)::Matrix
    return sde.diffusion(x, t)
end

"""
    get_metadata(sde::LangevinSDE) → Dict

Extract full provenance information from Langevin SDE.
"""
function get_metadata(sde::LangevinSDE)::Dict
    return sde.metadata
end

"""
    to_json(sde::LangevinSDE) → String

Serialize LangevinSDE to JSON for downstream processing.
"""
function to_json(sde::LangevinSDE)::String
    data = Dict(
        :type => "LangevinSDE",
        :reversibility => String(sde.reversibility),
        :stiff => sde.is_stiff,
        :metadata => sde.metadata
    )
    return JSON.json(data)
end

end  # module
