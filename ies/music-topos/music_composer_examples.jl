#!/usr/bin/env julia
#
# music_composer_examples.jl
#
# Interactive examples for ALPHA-BETA-GAMMA Music Composer
#

include("alpha_beta_gamma_composer.jl")

println("\n" * "="^80)
println("ALPHA-BETA-GAMMA MUSIC COMPOSER - Interactive Examples")
println("="^80)
println()

# =============================================================================
# Example 1: Basic Composition in C Major
# =============================================================================

println("Example 1: Basic C Major Composition")
println("-"^40)

# Simple ascending scale
c_major_seed = [
    Note(60, 1.0),  # C
    Note(62, 1.0),  # D
    Note(64, 1.0),  # E
    Note(65, 1.0),  # F
    Note(67, 1.0),  # G
    Note(69, 1.0),  # A
    Note(71, 1.0),  # B
    Note(72, 1.0)   # C'
]

c_major_world = MusicalWorld(0, :major)
c_major_comp = generate_composition(c_major_seed, c_major_world)

println(c_major_comp)
println()

# Export MIDI events
c_major_events = to_midi_events(c_major_comp)
println("Generated $(length(c_major_events)) MIDI events")
println("First event: $(c_major_events[1])")
println()

# =============================================================================
# Example 2: Modal Exploration - D Dorian
# =============================================================================

println("Example 2: D Dorian Modal Composition")
println("-"^40)

# Dorian characteristic: raised 6th scale degree
dorian_seed = [
    Note(62, 0.5),   # D
    Note(64, 0.5),   # E
    Note(65, 1.0),   # F
    Note(67, 0.5),   # G
    Note(69, 0.5),   # A
    Note(71, 1.0),   # B (characteristic raised 6th)
    Note(69, 0.5),   # A
    Note(67, 0.5)    # G
]

dorian_world = MusicalWorld(2, :dorian)
dorian_comp = generate_composition(dorian_seed, dorian_world,
    use_rubato=true, use_development=true)

println(dorian_comp)
println()

# =============================================================================
# Example 3: Minor Key with Development - A Minor
# =============================================================================

println("Example 3: A Minor with Development Section")
println("-"^40)

# Descending natural minor
a_minor_seed = [
    Note(69, 1.0),  # A
    Note(67, 1.0),  # G
    Note(65, 1.0),  # F
    Note(64, 1.0),  # E
    Note(62, 1.0),  # D
    Note(60, 1.0),  # C
    Note(62, 1.0),  # D
    Note(64, 1.0)   # E
]

a_minor_world = MusicalWorld(9, :minor)
a_minor_comp = generate_composition(a_minor_seed, a_minor_world,
    use_development=true)

println(a_minor_comp)
println()

# =============================================================================
# Example 4: Modulation - C Major to G Major
# =============================================================================

println("Example 4: Modulation from C Major to G Major")
println("-"^40)

c_major = MusicalWorld(0, :major)
g_major = MusicalWorld(7, :major)

modulation = find_modulation(c_major, g_major)
println("Source: $(modulation.source.name)")
println("Target: $(modulation.target.name)")
println("Pivot chord root: $(modulation.pivot_chord.root) ($(key_name(modulation.pivot_chord.root)))")
println()

# Compose in source key
c_major_phrase = [Note(60, 1.0), Note(62, 1.0), Note(64, 1.0), Note(65, 1.0)]
c_comp = generate_composition(c_major_phrase, c_major, generate_bass=false)

# Compose in target key
g_major_phrase = [Note(67, 1.0), Note(69, 1.0), Note(71, 1.0), Note(72, 1.0)]
g_comp = generate_composition(g_major_phrase, g_major, generate_bass=false)

println("C Major phrase tonality: $(round(tonality_score(c_comp), digits=3))")
println("G Major phrase tonality: $(round(tonality_score(g_comp), digits=3))")
println()

# =============================================================================
# Example 5: World Involution - Relative Keys
# =============================================================================

println("Example 5: World Involution (Relative Keys)")
println("-"^40)

e_major = MusicalWorld(4, :major)
println("Starting world: $(e_major.name)")
println("World entropy: $(round(world_entropy(e_major), digits=3))")

c_sharp_minor = involution(e_major)
println("Involution: $(c_sharp_minor.name)")
println("World entropy: $(round(world_entropy(c_sharp_minor), digits=3))")

e_major_again = involution(c_sharp_minor)
println("Double involution: $(e_major_again.name)")
println("Involution is self-inverse: $(e_major_again.name == e_major.name)")
println()

# =============================================================================
# Example 6: Scoped Operator Comparison
# =============================================================================

println("Example 6: Scoped Operator Effects")
println("-"^40)

base_melody = [Note(60, 1.0), Note(62, 1.0), Note(64, 1.0), Note(65, 1.0)]

cone_melody = apply_scope(base_melody, CONE_UP, 1.5)
descent_melody = apply_scope(base_melody, DESCENT_DOWN, 1.5)
adhesion_melody = apply_scope(base_melody, ADHESION_FLAT, 2.0)

println("Base melody pitches: $([n.pitch for n in base_melody])")
println("Cone (↑) pitches:    $([n.pitch for n in cone_melody])")
println("Descent (↓) pitches: $([n.pitch for n in descent_melody])")
println("Adhesion (↔) pitches: $([n.pitch for n in adhesion_melody])")
println()

# =============================================================================
# Example 7: Game Strategy Comparison
# =============================================================================

println("Example 7: Compositional Strategies")
println("-"^40)

theme_melody = [Note(60, 1.0), Note(64, 1.0), Note(67, 1.0), Note(72, 1.0)]

# Theme
theme_strategy = GameStrategy(THEME, Dict())
theme_result = apply_strategy(theme_melody, theme_strategy)

# Variation
variation_strategy = GameStrategy(VARIATION,
    Dict(:rhythm_factor => 1.5, :pitch_offset => 5))
variation_result = apply_strategy(theme_melody, variation_strategy)

# Development
development_strategy = GameStrategy(DEVELOPMENT,
    Dict(:fragment_size => 2, :transpose_step => 4))
development_result = apply_strategy(theme_melody, development_strategy)

# Recapitulation
recap_strategy = GameStrategy(RECAPITULATION, Dict(:transpose => 12))
recap_result = apply_strategy(theme_melody, recap_strategy)

println("Theme:          $([n.pitch for n in theme_result])")
println("Variation:      $([n.pitch for n in variation_result])")
println("Development:    $([n.pitch for n in development_result])")
println("Recapitulation: $([n.pitch for n in recap_result])")
println()

# =============================================================================
# Example 8: Triad Construction & Balance
# =============================================================================

println("Example 8: Triadic Harmony & GF(3) Balance")
println("-"^40)

root_c = Note(60)  # C

major_triad = Triad(60, :major)
minor_triad = Triad(60, :minor)
dim_triad = Triad(60, :diminished)
aug_triad = Triad(60, :augmented)

println("C Major:      [$(major_triad.root), $(major_triad.third), $(major_triad.fifth)] = [C, E, G]")
println("  Colors: $(major_triad.color), Balance: $(verify_triad_balance(major_triad))")

println("C Minor:      [$(minor_triad.root), $(minor_triad.third), $(minor_triad.fifth)] = [C, Eb, G]")
println("  Colors: $(minor_triad.color), Balance: $(verify_triad_balance(minor_triad))")

println("C Diminished: [$(dim_triad.root), $(dim_triad.third), $(dim_triad.fifth)] = [C, Eb, Gb]")
println("  Colors: $(dim_triad.color), Balance: $(verify_triad_balance(dim_triad))")

println("C Augmented:  [$(aug_triad.root), $(aug_triad.third), $(aug_triad.fifth)] = [C, E, G#]")
println("  Colors: $(aug_triad.color), Balance: $(verify_triad_balance(aug_triad))")
println()

# =============================================================================
# Example 9: Rhythmic Structure Application
# =============================================================================

println("Example 9: Rhythmic Structure & Subdivision")
println("-"^40)

simple_melody = [Note(60, 1.0), Note(62, 1.0), Note(64, 1.0), Note(65, 1.0)]

# 4/4 meter with dotted rhythm
rhythm_4_4 = RhythmicStructure(
    (4, 4),                      # 4/4 time
    4,                           # 4-beat phrases
    [1.5, 0.5, 1.0, 1.0]        # Long-short-even-even
)

rhythmic_melody = apply_rhythm(simple_melody, rhythm_4_4)

println("Original durations: $([n.duration for n in simple_melody])")
println("Rhythmic durations: $([n.duration for n in rhythmic_melody])")
println("Subdivision pattern: $(rhythm_4_4.subdivision)")
println()

# =============================================================================
# Example 10: Full Sonata-Style Form
# =============================================================================

println("Example 10: Sonata-Style Form (Exposition-Development-Recapitulation)")
println("-"^40)

# Exposition theme in C major
exposition_seed = [Note(60, 1.0), Note(64, 1.0), Note(67, 1.0), Note(72, 1.0)]
exposition_world = MusicalWorld(0, :major)

# Development in relative minor
development_seed = [Note(69, 0.5), Note(67, 0.5), Note(65, 1.0), Note(64, 1.0)]
development_world = MusicalWorld(9, :minor)

# Recapitulation back in C major
recap_seed = [Note(72, 1.0), Note(67, 1.0), Note(64, 1.0), Note(60, 2.0)]
recap_world = MusicalWorld(0, :major)

exposition = generate_composition(exposition_seed, exposition_world,
    use_rubato=false, use_development=false)
development = generate_composition(development_seed, development_world,
    use_rubato=true, use_development=true)
recapitulation = generate_composition(recap_seed, recap_world,
    use_rubato=false, use_development=false)

println("EXPOSITION (C Major):")
println("  Length: $(length(exposition.melody)) notes")
println("  Tonality: $(round(tonality_score(exposition), digits=3))")

println("\nDEVELOPMENT (A Minor):")
println("  Length: $(length(development.melody)) notes")
println("  Tonality: $(round(tonality_score(development), digits=3))")
println("  Complexity: $(round(harmonic_complexity(development), digits=3))")

println("\nRECAPITULATION (C Major):")
println("  Length: $(length(recapitulation.melody)) notes")
println("  Tonality: $(round(tonality_score(recapitulation), digits=3))")
println()

# =============================================================================
# Summary
# =============================================================================

println("="^80)
println("Examples Complete!")
println("="^80)
println()
println("Demonstrated:")
println("  ✓ Basic composition generation")
println("  ✓ Modal exploration (Dorian)")
println("  ✓ Minor keys with development")
println("  ✓ Modulation between keys")
println("  ✓ World involution (relative keys)")
println("  ✓ Scoped operators (cone/descent/adhesion)")
println("  ✓ Game strategies (theme/variation/development/recap)")
println("  ✓ Triadic harmony with GF(3) balance")
println("  ✓ Rhythmic structure & subdivision")
println("  ✓ Large-scale form (sonata structure)")
println()
println("Ready for interactive use!")
println("="^80)
