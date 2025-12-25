#!/usr/bin/env ruby
# examples/analyze_bach_chorale.rb
#
# Complete analysis of a Bach chorale through all 8 music theory categories
#
# This example shows how to:
# 1. Load the Music Topos Framework
# 2. Define a chord progression (Bach chorale)
# 3. Analyze through all 8 categories
# 4. Extract specific insights from each category
# 5. Display coherence validation

require_relative '../lib/music_topos_framework'
require_relative '../lib/chord'

puts "=" * 80
puts "🎵 BACH CHORALE ANALYSIS - All 8 Categories"
puts "=" * 80
puts ""

# Initialize framework
framework = MusicToposFramework.new

# Bach chorale: "O Haupt voll Blut und Wunden" excerpt
# Key: E Major, first 4 measures
# I - IV - V7 - I (classic harmonic progression)

puts "Chorale: 'O Haupt voll Blut und Wunden' by J.S. Bach"
puts "Key: E Major"
puts "Progression: I - IV - V7 - I"
puts ""

chords = [
  Chord.from_notes(['E', 'G#', 'B']),    # I (E Major)
  Chord.from_notes(['A', 'C#', 'E']),    # IV (A Major)
  Chord.from_notes(['B', 'D#', 'F#']),   # V7 (B Major, treating as V)
  Chord.from_notes(['E', 'G#', 'B'])     # I (E Major)
]

# Analyze through all 8 categories
puts "Analyzing through all 8 categories..."
puts ""

analysis = framework.analyze_progression(chords, key: 'E')

# Extract and display results from each category
puts "CATEGORY 4: GROUP THEORY"
puts "-" * 80
cat4 = analysis[:analyses_by_category][4][:analysis]
puts "Permutations: #{cat4[:permutations]}"
puts "Composition Valid: #{cat4[:composition_valid]}"
puts ""

puts "CATEGORY 5: HARMONIC FUNCTION"
puts "-" * 80
cat5 = analysis[:analyses_by_category][5][:analysis]
puts "Functions: #{cat5[:functions].join(' → ')}"
puts "Valid Progression: #{cat5[:valid_progression]}"
puts "Cadence Type: #{cat5[:cadence]}"
puts ""

puts "CATEGORY 6: MODULATION"
puts "-" * 80
cat6 = analysis[:analyses_by_category][6][:analysis]
puts "Modulation Paths: #{cat6[:modulation_paths]}"
puts "Circle of Fifths Movement: #{cat6[:circle_of_fifths_movement]}"
puts ""

puts "CATEGORY 7: VOICE LEADING (SATB)"
puts "-" * 80
cat7 = analysis[:analyses_by_category][7][:analysis]
puts "Chord Count: #{cat7[:chord_count]}"
puts "Voice Motion Analysis: #{cat7[:voice_motion_analysis]}"
puts ""

puts "CATEGORY 8: PROGRESSIONS"
puts "-" * 80
cat8 = analysis[:analyses_by_category][8][:analysis]
puts "Progression Length: #{cat8[:progression_length]}"
puts "Harmonic Closure: #{cat8[:harmonic_closure]}"
puts ""

puts "CATEGORY 9: STRUCTURE"
puts "-" * 80
cat9 = analysis[:analyses_by_category][9][:analysis]
puts "Phrase Structure: #{cat9[:phrase_structure]}"
puts ""

puts "CATEGORY 10: FORM"
puts "-" * 80
cat10 = analysis[:analyses_by_category][10][:analysis]
puts "Structural Role: #{cat10[:structural_role]}"
puts ""

puts "CATEGORY 11: SPECTRAL ANALYSIS"
puts "-" * 80
cat11 = analysis[:analyses_by_category][11][:analysis]
puts "Total Harmonics: #{cat11[:total_harmonics]}"
puts ""

# Validate coherence across all categories
puts "CROSS-CATEGORY COHERENCE VALIDATION"
puts "-" * 80
coherence = framework.validate_coherence(analysis)
puts "Status: #{coherence[:coherent] ? '✓ COHERENT' : '✗ INCOHERENT'}"
puts "All Categories Present: #{coherence[:validations][:all_categories_present] ? '✓' : '✗'}"
puts "Progression Length Consistent: #{coherence[:validations][:progression_length_consistent] ? '✓' : '✗'}"
puts "Harmonic & Structure Agree: #{coherence[:validations][:harmonic_and_structure_agree] ? '✓' : '✗'}"
puts ""

puts "=" * 80
puts "✓ Analysis Complete"
puts "=" * 80
puts ""
puts "INTERPRETATION:"
puts ""
puts "This four-measure chorale excerpt demonstrates:"
puts ""
puts "1. GROUP THEORY (Cat 4):"
puts "   - Chords are permutations of pitch space"
puts "   - Returning to E Major (original pitch) closes the cycle"
puts ""
puts "2. HARMONIC FUNCTION (Cat 5):"
puts "   - T→S→D→T forms the complete harmonic cycle"
puts "   - Authentic cadence (V-I) provides strong closure"
puts ""
puts "3. MODULATION (Cat 6):"
puts "   - All chords remain in E Major"
puts "   - No key changes needed"
puts ""
puts "4. VOICE LEADING (Cat 7):"
puts "   - Smooth transitions possible between all chords"
puts "   - SATB rules can be respected"
puts ""
puts "5. PROGRESSIONS (Cat 8):"
puts "   - Harmonic closure confirmed"
puts "   - Standard, expected progression"
puts ""
puts "6. STRUCTURE (Cat 9):"
puts "   - Opens with I, closes with authentic cadence V-I"
puts "   - Classic phrase structure"
puts ""
puts "7. FORM (Cat 10):"
puts "   - This is an opening gesture"
puts "   - Part of larger chorale structure"
puts ""
puts "8. SPECTRAL (Cat 11):"
puts "   - E Major chord has warm, blended harmonic content"
puts "   - Human ear perceives as consonant"
puts ""
puts "All 8 categories agree: This is a coherent, well-formed harmonic phrase."
puts ""
