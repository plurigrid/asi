#!/usr/bin/env ruby
# examples/jazz_ii_v_i_analysis.rb
#
# Analyze the most common jazz progression: ii-V-I
#
# This example shows how to:
# 1. Analyze a jazz standard progression
# 2. Extract harmonic function analysis
# 3. Compare with classical music theory
# 4. Use the API for category-specific analysis

require_relative '../lib/music_topos_framework'
require_relative '../lib/chord'

puts "=" * 80
puts "🎷 JAZZ STANDARD: ii-V-I Progression Analysis"
puts "=" * 80
puts ""

framework = MusicToposFramework.new

# ii-V-I in C Major
# D minor 7, G dominant 7, C major
puts "Progression: ii-V-I in C Major"
puts "Chords: Dm7 - G7 - Cmaj7"
puts "Roman Numerals: ii - V - I"
puts ""

chords = [
  Chord.from_notes(['D', 'F', 'A']),     # ii (D minor, simplified)
  Chord.from_notes(['G', 'B', 'D']),     # V (G dominant, simplified)
  Chord.from_notes(['C', 'E', 'G'])      # I (C major)
]

# Full analysis
puts "FULL ANALYSIS (All 8 Categories)"
puts "-" * 80
analysis = framework.analyze_progression(chords, key: 'C')

# Harmonic function focus
puts ""
puts "HARMONIC FUNCTION ANALYSIS (Category 5)"
puts "-" * 80
cat5 = analysis[:analyses_by_category][5][:analysis]
puts "Functions: #{cat5[:functions].join(' → ')}"
puts "Valid Progression: #{cat5[:valid_progression] ? '✓ YES' : '✗ NO'}"
puts "Cadence: #{cat5[:cadence].to_s.upcase}"
puts ""

# Interpretation
puts "MUSICAL INTERPRETATION"
puts "-" * 80
puts ""
puts "The ii-V-I progression is fundamental in jazz for these reasons:"
puts ""
puts "1. Functional Harmony:"
puts "   - Dm7 (ii): Subdominant, begins harmonic movement"
puts "   - G7 (V): Dominant, creates tension and pull"
puts "   - Cmaj7 (I): Tonic, provides resolution"
puts "   - Forms complete T→S→D→T cycle"
puts ""
puts "2. Voice Leading Opportunity:"
puts "   - Smooth voice leading possible"
puts "   - Chromatic connections available"
puts "   - Tritone substitutions possible (Db7 for G7)"
puts ""
puts "3. Cadential Function:"
puts "   - V-I authentic cadence is strongest resolution"
puts "   - Used in almost every jazz standard"
puts "   - Forms basis for improvisation"
puts ""
puts "4. Repetition Pattern:"
puts "   - In jazz, ii-V-I often repeats in different keys"
puts "   - Creates sense of harmonic journey"
puts "   - Allows modulation through transposition"
puts ""

puts ""
puts "CATEGORY-BY-CATEGORY BREAKDOWN"
puts "-" * 80
puts ""

# Category 4: Group Theory
cat4 = analysis[:analyses_by_category][4][:analysis]
puts "[4] GROUP THEORY"
puts "    Three different pitch classes in clear progression"
puts "    Dm→G→C forms descending fifth pattern"
puts ""

# Category 5: Harmonic Function
puts "[5] HARMONIC FUNCTION"
puts "    Perfect S→D→T demonstration"
puts "    All valid jazz progressions contain this core"
puts ""

# Category 6: Modulation
cat6 = analysis[:analyses_by_category][6][:analysis]
puts "[6] MODULATION"
puts "    No modulation in basic ii-V-I"
puts "    But cycle can repeat in different keys:"
puts "    - ii-V-I in C"
puts "    - ii-V-I in G (modulation up a fifth)"
puts "    - ii-V-I in F (modulation down a fourth)"
puts ""

# Category 7: Voice Leading
puts "[7] VOICE LEADING"
puts "    Natural voice leading:"
puts "    D-F-A → G-B-D → C-E-G"
puts "    Minimal motion if each note moves up slightly"
puts ""

# Category 8: Progressions
cat8 = analysis[:analyses_by_category][8][:analysis]
puts "[8] PROGRESSIONS"
puts "    Harmonic closure: ✓ #{cat8[:harmonic_closure]}"
puts "    One of the most common progressions in music"
puts ""

# Category 9: Structure
puts "[9] STRUCTURE"
puts "    Typically spans 2-4 measures"
puts "    Often used as turnaround (return to top)"
puts "    Provides cadential clarity"
puts ""

# Category 10: Form
puts "[10] FORM"
puts "    In AABA or ABAC structures,"
puts "    ii-V-I often appears in both A and B sections"
puts "    Creates harmonic coherence"
puts ""

# Category 11: Spectral
puts "[11] SPECTRAL"
puts "    D minor: slightly darker (more minor thirds)"
puts "    G dominant: complex (tritone creates tension)"
puts "    C major: bright, clear, resolved"
puts ""

puts "=" * 80
puts "✓ Analysis Complete"
puts "=" * 80
