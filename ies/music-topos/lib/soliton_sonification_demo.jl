#!/usr/bin/env julia
# lib/soliton_sonification_demo.jl
#
# Demonstration: Topological Solitons → Musical Composition
#
# Workflow:
# 1. Create simplicial complex (musical topology)
# 2. Compute Hodge Laplacian (topological operator)
# 3. Extract solitons from zero-modes (topological defects)
# 4. Apply anyonic fusion algebra (braiding statistics)
# 5. Sonify to musical events (pitch, timbre, rhythm)
# 6. Arrange into score (composition)

using LinearAlgebra, SparseArrays, Statistics

include("topological_solitons_anyons.jl")

# =============================================================================
# SIMPLICIAL COMPLEX CONSTRUCTION
# =============================================================================

"""
Create a musical simplicial complex from a composition sketch
Maps musical structure to topological cells:
- 0-cells: Notes
- 1-cells: Intervals (pitch relationships)
- 2-cells: Chords (harmonic relationships)
- 3-cells: Progressions (temporal structure)
"""
struct MusicalSimplicialComplex
    # Boundary operators at each dimension
    boundary_0::SparseMatrixCSC  # Empty (0-cells are minimal)
    boundary_1::SparseMatrixCSC  # Note → Interval edges
    boundary_2::SparseMatrixCSC  # Interval → Chord faces

    # Number of cells at each dimension
    num_0cells::Int              # Notes
    num_1cells::Int              # Intervals
    num_2cells::Int              # Chords

    # Cell content (labels)
    cell_0_labels::Vector{String}  # Note names
    cell_1_labels::Vector{String}  # Interval names
    cell_2_labels::Vector{String}  # Chord names
end

"""
Create a simple C major scale as a simplicial complex
C-D-E-F-G-A-B form a 0-skeleton
Intervals form 1-skeleton (edges)
Triads (chords) form 2-skeleton (triangles)
"""
function create_c_major_complex()::MusicalSimplicialComplex
    # 0-cells: C D E F G A B
    notes = ["C", "D", "E", "F", "G", "A", "B"]
    num_notes = length(notes)

    # 1-cells: consecutive intervals
    # C-D, D-E, E-F, F-G, G-A, A-B, B-C (wraps)
    num_intervals = num_notes
    interval_names = ["C-D", "D-E", "E-F", "F-G", "G-A", "A-B", "B-C"]

    # Boundary operator ∂₁: maps intervals to their endpoints
    # Each interval i connects notes i and (i+1)%7
    boundary_1 = spzeros(Int, num_notes, num_intervals)
    for i in 1:num_intervals
        boundary_1[i, i] = 1                                  # Start note
        boundary_1[mod(i, num_notes) + 1, i] = -1            # End note (orientation)
    end

    # 2-cells: triads (major chords built on each note)
    # C major: C-E-G, D minor: D-F-A, E minor: E-G-B, etc.
    num_chords = num_notes
    chord_names = [
        "C major", "D minor", "E minor", "F major",
        "G major", "A minor", "B dim"
    ]

    # Boundary operator ∂₂: maps chords to their boundary intervals
    # Each chord uses 3 intervals
    boundary_2 = spzeros(Int, num_intervals, num_chords)

    triad_intervals = [
        (1, 3, 5),     # C major: C-D-E, D-E-F, E-F-G gap patterns
        (2, 4, 6),     # D minor
        (3, 5, 7),     # E minor
        (4, 6, 1),     # F major
        (5, 7, 2),     # G major
        (6, 1, 3),     # A minor
        (7, 2, 4),     # B diminished
    ]

    for (chord_idx, (i1, i2, i3)) in enumerate(triad_intervals)
        boundary_2[i1, chord_idx] = 1
        boundary_2[i2, chord_idx] = 1
        boundary_2[i3, chord_idx] = 1
    end

    boundary_0 = spzeros(Int, 0, num_notes)  # Empty

    MusicalSimplicialComplex(
        boundary_0, boundary_1, boundary_2,
        num_notes, num_intervals, num_chords,
        notes, interval_names, chord_names
    )
end

# =============================================================================
# HODGE LAPLACIAN COMPUTATION FOR MUSICAL TOPOLOGY
# =============================================================================

"""
Compute Hodge Laplacian on musical simplicial complex
L₁ = ∂₂ᵀ ∂₂ + ∂₁ ∂₁ᵀ
"""
function compute_musical_hodge_laplacian(
    complex::MusicalSimplicialComplex
)::Tuple{SparseMatrixCSC, Vector{Float64}, Matrix{Float64}}

    # L₁ = δ₁ δ₁ᵀ + ∂₁ ∂₁ᵀ
    # where δ₁ = ∂₂ᵀ (coboundary)

    # Downward part: ∂₁ ∂₁ᵀ
    down = complex.boundary_1 * complex.boundary_1'

    # Upward part: ∂₂ᵀ ∂₂
    up = complex.boundary_2' * complex.boundary_2

    # Total Laplacian (converted to dense for eigendecomposition)
    laplacian = down + up

    # Eigendecomposition
    eig = eigen(Matrix(laplacian))

    (laplacian, eig.values, eig.vectors)
end

# =============================================================================
# COMPLETE SONIFICATION PIPELINE
# =============================================================================

function soliton_composition_pipeline(
    composition_title::String = "Topological Soliton Sonata"
)

    println("╔════════════════════════════════════════════════════════════════╗")
    println("║  TOPOLOGICAL SOLITONS & ANYONIC STATISTICS IN MUSIC           ║")
    println("║  $(composition_title)                              ")
    println("╚════════════════════════════════════════════════════════════════╝")
    println()

    # ─────────────────────────────────────────────────────────────────────
    # Step 1: Create musical topology
    # ─────────────────────────────────────────────────────────────────────

    println("Step 1: Musical Topology")
    println("  Creating simplicial complex from C major scale...")
    complex = create_c_major_complex()
    println("  ✓ 0-cells (notes): $(complex.num_0cells)")
    println("  ✓ 1-cells (intervals): $(complex.num_1cells)")
    println("  ✓ 2-cells (chords): $(complex.num_2cells)")
    println()

    # ─────────────────────────────────────────────────────────────────────
    # Step 2: Compute Hodge Laplacian
    # ─────────────────────────────────────────────────────────────────────

    println("Step 2: Hodge Laplacian (Topological Operator)")
    println("  Computing L₁ = ∂₂ᵀ∂₂ + ∂₁∂₁ᵀ...")
    laplacian, eigvals, eigvecs = compute_musical_hodge_laplacian(complex)
    println("  ✓ Eigenvalues: ", round.(eigvals[1:min(5, length(eigvals))], digits=4))
    println()

    # ─────────────────────────────────────────────────────────────────────
    # Step 3: Detect topological solitons
    # ─────────────────────────────────────────────────────────────────────

    println("Step 3: Topological Soliton Detection")
    println("  Extracting zero-modes from Hodge Laplacian...")

    system = TopologicalSolitonSystem()
    process_hodge_laplacian!(system, eigvals, eigvecs, 1, base_note=60)

    println("  ✓ Detected $(length(system.solitons)) solitons")
    if !isempty(system.solitons)
        println("    Solitons by charge:")
        for sol in system.solitons
            println("      Charge $(sol.charge): $(sol.anyonic_type) " *
                   "(stability: $(sol.stability_category), " *
                   "polarity: $(sol.polarity))")
        end
    end
    println()

    # ─────────────────────────────────────────────────────────────────────
    # Step 4: Apply anyonic fusion algebra
    # ─────────────────────────────────────────────────────────────────────

    println("Step 4: Anyonic Fusion Algebra")
    println("  Applying braiding statistics to solitons...")

    # Generate fusion/braiding examples
    if length(system.solitons) >= 2
        sol1 = system.solitons[1]
        sol2 = system.solitons[min(2, length(system.solitons))]

        fusion_result = fuse(system.algebra, sol1.anyonic_type, sol2.anyonic_type)
        braiding_angle_val = braiding_angle(system.algebra, sol1.anyonic_type, sol2.anyonic_type)

        println("  ✓ Fusion: $(sol1.anyonic_type) ⊗ $(sol2.anyonic_type) → $fusion_result")
        println("  ✓ Braiding angle: $(round(braiding_angle_val * 180 / π, digits=1))°")
    end
    println()

    # ─────────────────────────────────────────────────────────────────────
    # Step 5: Generate musical score
    # ─────────────────────────────────────────────────────────────────────

    println("Step 5: Musical Score Generation")
    println("  Converting solitons to musical events...")
    println()

    if !isempty(system.events)
        println("  ┌────────────────────────────────────────────────────┐")
        println("  │ Musical Events from Solitons                       │")
        println("  ├────────────────────────────────────────────────────┤")

        for (i, event) in enumerate(system.events[1:min(5, length(system.events))])
            note_name = get_note_name(event.pitch)
            harm_str = length(event.harmonics) > 1 ?
                      "$(event.harmonics[1]) + $(event.harmonics[2])" :
                      "$(event.harmonics[1])"

            println("  │ $(lpad(i, 2)). Note: $(rpad(note_name, 4)) | " *
                   "Vel: $(lpad(Int(event.velocity), 3)) | " *
                   "Dur: $(round(event.duration, digits=2)) beats")
            println("  │     Charge: $(event.charge) | Type: $(event.anyonic_type) | " *
                   "Polarity: $(event.polarity)")
        end

        println("  └────────────────────────────────────────────────────┘")
    end
    println()

    # ─────────────────────────────────────────────────────────────────────
    # Step 6: Harmonic analysis
    # ─────────────────────────────────────────────────────────────────────

    println("Step 6: Topological Invariants Summary")
    println()

    if !isempty(system.solitons)
        total_charge = sum(sol.charge for sol in system.solitons)
        avg_stability = mean(sol.stability_margin for sol in system.solitons)

        println("  Topological Properties:")
        println("    • Total charge (Gauss law): $total_charge")
        println("    • Mean stability margin: $(round(avg_stability, digits=3))")
        println("    • Dimension of Hodge Laplacian: $(length(eigvals))")
        println("    • Spectral gap: $(round(eigvals[2] - eigvals[1], digits=6))")
    end
    println()

    println("╔════════════════════════════════════════════════════════════════╗")
    println("║ Composition Ready: Topological Soliton Music Generation        ║")
    println("║ Based on: Hodge cohomology + Anyonic braiding statistics      ║")
    println("║ Ready for sonification to MIDI/audio output                   ║")
    println("╚════════════════════════════════════════════════════════════════╝")
    println()

    system
end

# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

"""
Convert MIDI pitch number to note name
"""
function get_note_name(midi_pitch::Float64)::String
    note_names = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
    rounded_pitch = round(Int, midi_pitch)
    octave = div(rounded_pitch, 12) - 1
    note_index = mod(rounded_pitch, 12) + 1
    note_names[note_index] * string(octave)
end

# =============================================================================
# MAIN DEMO
# =============================================================================

function main()
    system = soliton_composition_pipeline("Soliton Sonata in Topological C Major")
    system
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end

export MusicalSimplicialComplex, create_c_major_complex
export compute_musical_hodge_laplacian
export soliton_composition_pipeline, get_note_name
