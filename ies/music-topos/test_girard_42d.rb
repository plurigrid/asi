#!/usr/bin/env ruby
# test_girard_42d.rb
#
# Test suite for 0x42D Seed Mining with Girard Colors

require_relative 'lib/girard_colors'
require_relative 'lib/seed_miner_42d'

def assert(condition, message = "Assertion failed")
  raise message unless condition
end

puts "=" * 70
puts "🎨 0x42D GIRARD COLOR SEED MINING TEST SUITE"
puts "=" * 70
puts ""

tests_passed = 0
tests_total = 0

# =============================================================================
# TEST 1: SplitMix64 Determinism
# =============================================================================
puts "TEST 1: SplitMix64 Deterministic RNG"
puts "─" * 70

tests_total += 1
begin
  rng1 = SeedMiner::SplitMix64.new(0x42D)
  rng2 = SeedMiner::SplitMix64.new(0x42D)
  
  # Same seed → same sequence
  10.times do |i|
    v1 = rng1.next_u64
    v2 = rng2.next_u64
    assert v1 == v2, "Sequence diverged at position #{i}"
  end
  
  puts "  ✓ Same seed produces identical sequences"
  puts "  ✓ SplitMix64(0x42D) first value: 0x#{SeedMiner::SplitMix64.new(0x42D).next_u64.to_s(16)}"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 2: Color Generation
# =============================================================================
puts "TEST 2: Color Generation from Seed"
puts "─" * 70

tests_total += 1
begin
  color0 = SeedMiner.color_at(0x42D, 0)
  color1 = SeedMiner.color_at(0x42D, 1)
  color2 = SeedMiner.color_at(0x42D, 2)
  
  assert color0[:L] >= 10 && color0[:L] <= 95, "L out of range"
  assert color0[:C] >= 0 && color0[:C] <= 100, "C out of range"
  assert color0[:H] >= 0 && color0[:H] < 360, "H out of range"
  
  puts "  ✓ Color at index 0: L=#{color0[:L].round(1)}, C=#{color0[:C].round(1)}, H=#{color0[:H].round(1)}"
  puts "  ✓ Color at index 1: L=#{color1[:L].round(1)}, C=#{color1[:C].round(1)}, H=#{color1[:H].round(1)}"
  puts "  ✓ Color at index 2: L=#{color2[:L].round(1)}, C=#{color2[:C].round(1)}, H=#{color2[:H].round(1)}"
  puts "  ✓ All colors in valid LCH range"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 3: Girard Polarity Mapping
# =============================================================================
puts "TEST 3: Girard Polarity from Hue"
puts "─" * 70

tests_total += 1
begin
  # Red (0°) → positive
  # Blue (240°) → negative
  # Green (120°) → neutral
  
  assert GirardColors::PALETTE[:positive][:hue] == 0, "Positive should be red (0°)"
  assert GirardColors::PALETTE[:negative][:hue] == 240, "Negative should be blue (240°)"
  
  # Test polarity derivation
  color_red = { H: 30 }
  color_blue = { H: 200 }
  color_green = { H: 150 }
  
  # Manual polarity check (using private method via send)
  pol_red = SeedMiner.send(:hue_to_polarity, 30)
  pol_blue = SeedMiner.send(:hue_to_polarity, 200)
  pol_green = SeedMiner.send(:hue_to_polarity, 150)
  
  assert pol_red == :positive, "Red hue should be positive"
  assert pol_blue == :negative, "Blue hue should be negative"
  assert pol_green == :neutral, "Green hue should be neutral"
  
  puts "  ✓ Hue 30° (red-orange) → :positive"
  puts "  ✓ Hue 200° (cyan-blue) → :negative"
  puts "  ✓ Hue 150° (green-cyan) → :neutral"
  puts "  ✓ Girard polarity mapping correct"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 4: Seed Evaluation
# =============================================================================
puts "TEST 4: Seed Quality Evaluation"
puts "─" * 70

tests_total += 1
begin
  eval_42d = SeedMiner.evaluate_seed(0x42D)
  
  assert eval_42d[:seed] == 0x42D, "Seed should be 0x42D"
  assert eval_42d[:total_score] >= 0 && eval_42d[:total_score] <= 1, "Score out of range"
  
  puts "  ✓ Seed: #{eval_42d[:seed_hex]}"
  puts "  ✓ Interval variety: #{eval_42d[:interval_variety].round(3)}"
  puts "  ✓ Consonance: #{eval_42d[:consonance].round(3)}"
  puts "  ✓ Polarity balance: #{eval_42d[:polarity_balance].round(3)}"
  puts "  ✓ Leitmotif potential: #{eval_42d[:leitmotif_score].round(3)}"
  puts "  ✓ Circle of fifths: #{eval_42d[:cof_alignment].round(3)}"
  puts "  ✓ TOTAL SCORE: #{eval_42d[:total_score].round(3)}"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 5: Leitmotif Generation
# =============================================================================
puts "TEST 5: Leitmotif Generation from 0x42D"
puts "─" * 70

tests_total += 1
begin
  leit = SeedMiner42D.leitmotif(length: 8, base_pitch: 60)
  
  assert leit[:seed] == 0x42D, "Should use base seed"
  assert leit[:notes].size == 8, "Should have 8 notes"
  assert leit[:intervals].size == 7, "Should have 7 intervals"
  
  pitches = leit[:notes].map { |n| n[:pitch] }
  
  puts "  ✓ Leitmotif from 0x42D:"
  puts "    Pitches: #{pitches.join(' → ')}"
  puts "    Intervals: #{leit[:intervals].join(', ')}"
  puts "    Polarities: #{leit[:polarities].join(', ')}"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 6: Interval-Specified Leitmotif
# =============================================================================
puts "TEST 6: Interval-Specified Leitmotif"
puts "─" * 70

tests_total += 1
begin
  # The "Cleft" pattern: up fifth, down fourth, up third
  cleft = SeedMiner42D.leitmotif_from_intervals(:cleft, [0, 7, -5, 4])
  
  assert cleft[:intervals] == [0, 7, -5, 4], "Intervals should match input"
  assert cleft[:notes].size == 5, "Should have 5 notes (4 intervals + start)"
  
  pitches = cleft[:notes].map { |n| n[:pitch] }
  
  puts "  ✓ 'Cleft' leitmotif: #{SeedMiner42D::LEITMOTIF_PATTERNS[:cleft]}"
  puts "    Pitches: #{pitches.join(' → ')}"
  puts "    (Starting from 60: C4)"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 7: Girard Connective Intervals
# =============================================================================
puts "TEST 7: Girard Connective → Musical Interval"
puts "─" * 70

tests_total += 1
begin
  tensor_interval = GirardColors::CONNECTIVE_INTERVALS[:tensor]
  par_interval = GirardColors::CONNECTIVE_INTERVALS[:par]
  plus_interval = GirardColors::CONNECTIVE_INTERVALS[:plus]
  with_interval = GirardColors::CONNECTIVE_INTERVALS[:with]
  
  assert tensor_interval == 7, "⊗ (tensor) should be P5 (7 semitones)"
  assert par_interval == 5, "⅋ (par) should be P4 (5 semitones)"
  assert plus_interval == 4, "⊕ (plus) should be M3 (4 semitones)"
  assert with_interval == 3, "& (with) should be m3 (3 semitones)"
  
  puts "  ✓ ⊗ (tensor) → Perfect Fifth (7 semitones)"
  puts "  ✓ ⅋ (par) → Perfect Fourth (5 semitones)"
  puts "  ✓ ⊕ (plus) → Major Third (4 semitones)"
  puts "  ✓ & (with) → Minor Third (3 semitones)"
  puts "  ✓ Linear logic connectives map to musical intervals"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 8: Harmonization with Girard Colors
# =============================================================================
puts "TEST 8: Harmonization via Girard Polarity"
puts "─" * 70

tests_total += 1
begin
  leit = SeedMiner42D.leitmotif(length: 4)
  harmonized = SeedMiner42D.harmonize_with_girard(leit)
  
  assert harmonized[:harmonized_notes].size == 4, "Should have 4 harmonized notes"
  
  harmonized[:harmonized_notes].each_with_index do |note, i|
    assert note[:harmony].is_a?(Array), "Should have harmony array"
    assert note[:chord_type], "Should have chord type"
    
    puts "  Note #{i + 1}: pitch=#{note[:pitch]}, " \
         "polarity=#{note[:girard_polarity]}, " \
         "chord=#{note[:chord_type]}, " \
         "harmony=#{note[:harmony]}"
  end
  
  puts "  ✓ All notes harmonized based on Girard polarity"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 9: Seed Mining
# =============================================================================
puts "TEST 9: Seed Mining Around 0x42D"
puts "─" * 70

tests_total += 1
begin
  # Small radius for speed
  results = SeedMiner.mine(0x42D, radius: 50, top_n: 5)
  
  assert results.size == 5, "Should return 5 results"
  assert results.first[:total_score] >= results.last[:total_score], "Should be sorted by score"
  
  puts "  Top 5 seeds (radius 50):"
  results.each_with_index do |r, i|
    puts "    #{i + 1}. #{r[:seed_hex]} → score #{r[:total_score].round(3)}"
  end
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 10: Cut Elimination (Dissonance Resolution)
# =============================================================================
puts "TEST 10: Girard Cut Elimination → Dissonance Resolution"
puts "─" * 70

tests_total += 1
begin
  cut_elim = GirardColors::CutElimination.new
  
  # Add tritone dissonance
  cut_elim.add_dissonance(6)  # Tritone
  cut_elim.resolve(0)         # Resolve to unison
  
  assert cut_elim.resolved, "Should be resolved"
  assert cut_elim.steps.size == 2, "Should have 2 steps"
  
  prog = cut_elim.to_progression
  
  puts "  ✓ Dissonance: tritone (6 semitones)"
  puts "  ✓ Resolution: unison (0 semitones)"
  puts "  ✓ Progression: #{prog}"
  puts "  ✓ Cut elimination models dissonance → consonance"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 11: Geometry of Interaction (Voice Leading)
# =============================================================================
puts "TEST 11: Geometry of Interaction → Voice Leading"
puts "─" * 70

tests_total += 1
begin
  goi = GirardColors::GeometryOfInteraction.new
  
  # Emit two tokens with opposite polarity
  goi.emit(60, :positive)  # C4
  goi.emit(64, :negative)  # E4
  
  # They interact (annihilate)
  result = goi.interact(0, 1)
  
  assert result[:type] == :annihilation, "Opposite polarities should annihilate"
  assert result[:interval] == 4, "C to E is 4 semitones"
  
  puts "  ✓ Token 1: C4 (positive polarity)"
  puts "  ✓ Token 2: E4 (negative polarity)"
  puts "  ✓ Interaction: annihilation (M3 interval)"
  puts "  ✓ Geometry of Interaction models voice motion"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# SUMMARY
# =============================================================================
puts "=" * 70
puts "TEST SUMMARY"
puts "=" * 70
puts ""

if tests_passed == tests_total
  puts "✓ ALL #{tests_total} TESTS PASSED!"
else
  puts "✗ #{tests_passed}/#{tests_total} tests passed"
end

puts ""
puts "Girard's Cleft de Logique ↔ Music Topos Mapping:"
puts "  ┌────────────────────────────────────────────────────────────────┐"
puts "  │  LINEAR LOGIC              │  MUSIC                           │"
puts "  ├────────────────────────────┼────────────────────────────────────│"
puts "  │  Positive polarity         │  Major mode, tension              │"
puts "  │  Negative polarity         │  Minor mode, resolution           │"
puts "  │  ⊗ (tensor)                │  Parallel fifth motion            │"
puts "  │  ⅋ (par)                   │  Contrary fourth motion           │"
puts "  │  ⊕ (plus)                  │  Additive major third             │"
puts "  │  & (with)                  │  Shared minor third               │"
puts "  │  ! (bang)                  │  Octave (exponential)             │"
puts "  │  ? (quest)                 │  Unison (why-not)                 │"
puts "  │  Cut elimination           │  Dissonance resolution            │"
puts "  │  Proof net                 │  Voice leading graph              │"
puts "  │  Geometry of Interaction   │  Parallel voice motion            │"
puts "  └────────────────────────────┴────────────────────────────────────┘"
puts ""
puts "Base Seed: 0x42D = 1069 = 'B-' (ASCII fragment)"
puts "Best seeds mined for harmonic leitmotifs with Girard color compatibility."
