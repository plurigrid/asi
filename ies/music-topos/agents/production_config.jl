"""
    ProductionConfig

Production configuration for 5,652+ theorem catalog across 6 provers.

Phase 4: Production Integration
===============================

Configures:
- Prover endpoints and capabilities
- Theorem catalog loading
- Performance tuning parameters
- Health thresholds per prover
"""

module ProductionConfig

using Dates

export
    ProverConfig,
    ProductionSettings,
    load_production_config,
    get_prover_config,
    get_all_provers,
    validate_config

# ============================================================================
# Part 1: Data Structures
# ============================================================================

"""
    ProverConfig

Configuration for a single theorem prover.
"""
struct ProverConfig
    name::Symbol                          # :dafny, :lean4, :stellogen, :coq, :agda, :idris2
    enabled::Bool                         # Whether prover is active
    priority::Int                         # Execution priority (1 = highest)
    timeout_seconds::Float64              # Max proof attempt time
    max_parallel::Int                     # Max concurrent proofs
    health_threshold::Float64             # Min acceptable gap
    theorem_path::String                  # Path to theorem files
    capabilities::Vector{Symbol}          # [:linear_types, :dependent_types, etc.]
end

"""
    ProductionSettings

Global production settings for the spectral architecture.
"""
mutable struct ProductionSettings
    # Catalog
    total_theorems::Int
    theorems_per_batch::Int
    
    # Health monitoring
    global_health_threshold::Float64      # Ramanujan threshold (0.25)
    check_interval_seconds::Float64       # How often to check health
    alert_on_degradation::Bool
    
    # Performance
    max_concurrent_provers::Int
    cache_size_mb::Int
    enable_comprehension_discovery::Bool
    enable_automatic_remediation::Bool
    
    # Provers
    provers::Dict{Symbol, ProverConfig}
    
    # Metadata
    config_version::String
    last_updated::DateTime
end

# ============================================================================
# Part 2: Default Configuration
# ============================================================================

"""
Default prover configurations for production.
"""
function default_prover_configs()::Dict{Symbol, ProverConfig}
    return Dict(
        :dafny => ProverConfig(
            :dafny,
            true,
            1,                              # Highest priority
            30.0,                           # 30s timeout
            4,                              # 4 parallel
            0.25,                           # Standard threshold
            "proofs/dafny/",
            [:linear_types, :refinement_types, :smt_backend]
        ),
        
        :lean4 => ProverConfig(
            :lean4,
            true,
            1,                              # Highest priority (tied with Dafny)
            45.0,                           # 45s timeout (more complex proofs)
            4,
            0.25,
            "proofs/lean4/",
            [:dependent_types, :tactics, :metaprogramming, :type_classes]
        ),
        
        :stellogen => ProverConfig(
            :stellogen,
            true,
            2,                              # Second priority
            20.0,                           # 20s timeout
            2,
            0.25,
            "proofs/stellogen/",
            [:proof_nets, :linear_logic, :game_semantics]
        ),
        
        :coq => ProverConfig(
            :coq,
            true,
            2,
            60.0,                           # 60s for complex tactics
            2,
            0.25,
            "proofs/coq/",
            [:dependent_types, :tactics, :extraction, :universe_polymorphism]
        ),
        
        :agda => ProverConfig(
            :agda,
            true,
            3,                              # Third priority
            45.0,
            2,
            0.25,
            "proofs/agda/",
            [:dependent_types, :cubical, :sized_types, :instance_arguments]
        ),
        
        :idris2 => ProverConfig(
            :idris2,
            true,
            3,
            30.0,
            2,
            0.25,
            "proofs/idris2/",
            [:dependent_types, :linear_types, :elaboration_reflection, :quantitative_types]
        )
    )
end

"""
    load_production_config() -> ProductionSettings

Load production configuration with defaults.
"""
function load_production_config()::ProductionSettings
    return ProductionSettings(
        # Catalog
        5652,                               # Total theorems in catalog
        100,                                # Batch size
        
        # Health monitoring
        0.25,                               # Ramanujan threshold
        60.0,                               # Check every 60 seconds
        true,                               # Alert on degradation
        
        # Performance
        6,                                  # All 6 provers can run
        512,                                # 512 MB cache
        true,                               # Enable comprehension discovery
        true,                               # Enable auto-remediation
        
        # Provers
        default_prover_configs(),
        
        # Metadata
        "1.0.0",
        now()
    )
end

# ============================================================================
# Part 3: Configuration Access
# ============================================================================

"""
    get_prover_config(settings, prover_name) -> ProverConfig

Get configuration for a specific prover.
"""
function get_prover_config(settings::ProductionSettings, prover_name::Symbol)::ProverConfig
    if !haskey(settings.provers, prover_name)
        error("Unknown prover: $prover_name")
    end
    return settings.provers[prover_name]
end

"""
    get_all_provers(settings; enabled_only=true) -> Vector{ProverConfig}

Get all prover configurations, optionally filtered by enabled status.
"""
function get_all_provers(settings::ProductionSettings; enabled_only::Bool=true)::Vector{ProverConfig}
    provers = collect(values(settings.provers))
    if enabled_only
        provers = filter(p -> p.enabled, provers)
    end
    # Sort by priority
    sort!(provers, by=p -> p.priority)
    return provers
end

"""
    get_provers_by_capability(settings, capability) -> Vector{ProverConfig}

Get provers that have a specific capability.
"""
function get_provers_by_capability(settings::ProductionSettings, capability::Symbol)::Vector{ProverConfig}
    provers = get_all_provers(settings)
    return filter(p -> capability in p.capabilities, provers)
end

# ============================================================================
# Part 4: Validation
# ============================================================================

"""
    validate_config(settings) -> (valid::Bool, errors::Vector{String})

Validate production configuration.
"""
function validate_config(settings::ProductionSettings)::Tuple{Bool, Vector{String}}
    errors = String[]
    
    # Check theorem count
    if settings.total_theorems <= 0
        push!(errors, "total_theorems must be positive")
    end
    
    # Check health threshold
    if settings.global_health_threshold < 0.0 || settings.global_health_threshold > 1.0
        push!(errors, "global_health_threshold must be in [0, 1]")
    end
    
    # Check provers
    if isempty(settings.provers)
        push!(errors, "At least one prover must be configured")
    end
    
    enabled_count = count(p -> p.enabled, values(settings.provers))
    if enabled_count == 0
        push!(errors, "At least one prover must be enabled")
    end
    
    # Check each prover
    for (name, prover) in settings.provers
        if prover.timeout_seconds <= 0
            push!(errors, "Prover $name: timeout must be positive")
        end
        if prover.max_parallel <= 0
            push!(errors, "Prover $name: max_parallel must be positive")
        end
        if prover.health_threshold < 0.0 || prover.health_threshold > 1.0
            push!(errors, "Prover $name: health_threshold must be in [0, 1]")
        end
    end
    
    return (isempty(errors), errors)
end

# ============================================================================
# Part 5: Configuration Display
# ============================================================================

function Base.show(io::IO, config::ProverConfig)
    status = config.enabled ? "✓" : "✗"
    println(io, "$status $(config.name) (priority=$(config.priority), timeout=$(config.timeout_seconds)s, parallel=$(config.max_parallel))")
end

function Base.show(io::IO, settings::ProductionSettings)
    println(io, "ProductionSettings v$(settings.config_version)")
    println(io, "  Theorems: $(settings.total_theorems)")
    println(io, "  Health threshold: $(settings.global_health_threshold)")
    println(io, "  Provers: $(length(settings.provers)) configured")
    for prover in get_all_provers(settings; enabled_only=false)
        println(io, "    ", prover)
    end
end

"""
    print_config_summary(settings)

Print a human-readable summary of the configuration.
"""
function print_config_summary(settings::ProductionSettings)
    println("=" ^ 60)
    println("PRODUCTION CONFIGURATION SUMMARY")
    println("=" ^ 60)
    println()
    
    println("Catalog:")
    println("  Total theorems: $(settings.total_theorems)")
    println("  Batch size: $(settings.theorems_per_batch)")
    println()
    
    println("Health Monitoring:")
    println("  Ramanujan threshold: $(settings.global_health_threshold)")
    println("  Check interval: $(settings.check_interval_seconds)s")
    println("  Alert on degradation: $(settings.alert_on_degradation)")
    println()
    
    println("Performance:")
    println("  Max concurrent provers: $(settings.max_concurrent_provers)")
    println("  Cache size: $(settings.cache_size_mb) MB")
    println("  Comprehension discovery: $(settings.enable_comprehension_discovery)")
    println("  Auto-remediation: $(settings.enable_automatic_remediation)")
    println()
    
    println("Provers ($(count(p -> p.enabled, values(settings.provers))) enabled):")
    for prover in get_all_provers(settings; enabled_only=false)
        status = prover.enabled ? "✓" : "✗"
        caps = join(string.(prover.capabilities), ", ")
        println("  $status $(prover.name)")
        println("      Priority: $(prover.priority), Timeout: $(prover.timeout_seconds)s")
        println("      Parallel: $(prover.max_parallel), Threshold: $(prover.health_threshold)")
        println("      Capabilities: $caps")
    end
    println()
    
    valid, errors = validate_config(settings)
    if valid
        println("✓ Configuration valid")
    else
        println("✗ Configuration errors:")
        for err in errors
            println("  - $err")
        end
    end
    
    println("=" ^ 60)
end

end  # module ProductionConfig
