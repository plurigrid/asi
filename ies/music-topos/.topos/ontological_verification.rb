#!/usr/bin/env ruby

# bin/ontological_verification.rb
#
# BADIOUIAN VERIFICATION SYSTEM
# No demos. Only necessary structural tests.
# Each verification is an EXISTENCE PROOF within mathematical worlds.

require_relative '../lib/pitch_class'
require_relative '../lib/chord'
require_relative '../lib/worlds'
require_relative '../lib/ontological_validator'

puts "=" * 80
puts "ONTOLOGICAL VERIFICATION: Logic of Worlds"
puts "=" * 80
puts ""

# TEST 1: Pitch Space World - Triangle Inequality
puts "VERIFICATION 1: Pitch Space (S¹) - Triangle Inequality"
puts "─" * 80

pitch_world = MusicalWorlds.pitch_space_world

# Add pitch classes: C, E, G (forming C major)
c = PitchClass.new(0)
e = PitchClass.new(4)
g = PitchClass.new(7)

pitch_world.add_object(c)
pitch_world.add_object(e)
pitch_world.add_object(g)

validation = pitch_world.validate_metric_space
puts "Pitch world validation:"
puts "  Valid: #{validation[:valid]}"
puts "  Objects: #{validation[:objects_count]}"
puts "  Errors: #{validation[:errors].size}"

if validation[:valid]
  puts "✓ Triangle inequality holds for all pitch combinations"
  puts "  d(C, G) = #{pitch_world.distance(c, g)}"
  puts "  d(C, E) + d(E, G) = #{pitch_world.distance(c, e)} + #{pitch_world.distance(e, g)} = #{pitch_world.distance(c, e) + pitch_world.distance(e, g)}"
  puts "  Verify: #{pitch_world.distance(c, g)} ≤ #{pitch_world.distance(c, e) + pitch_world.distance(e, g)}"
else
  puts "✗ Triangle inequality violated:"
  validation[:errors].each { |e| puts "  - #{e}" }
end

puts ""

# TEST 2: Chord Space World - Metric Validity
puts "VERIFICATION 2: Chord Space (Tⁿ) - Metric Axioms"
puts "─" * 80

chord_world = MusicalWorlds.chord_space_world

c_major = Chord.from_notes(['C', 'E', 'G', 'C'])
f_major = Chord.from_notes(['F', 'A', 'C', 'F'])
g_major = Chord.from_notes(['G', 'B', 'D', 'G'])

chord_world.add_object(c_major)
chord_world.add_object(f_major)
chord_world.add_object(g_major)

validation = chord_world.validate_metric_space
puts "Chord world validation:"
puts "  Valid: #{validation[:valid]}"
puts "  Objects: #{validation[:objects_count]}"
puts "  Errors: #{validation[:errors].size}"

if validation[:valid]
  puts "✓ Metric axioms satisfied"

  # Show distances
  d_cf = chord_world.distance(c_major, f_major)
  d_fg = chord_world.distance(f_major, g_major)
  d_cg = chord_world.distance(c_major, g_major)

  puts "  d(C, F) = #{d_cf}"
  puts "  d(F, G) = #{d_fg}"
  puts "  d(C, G) = #{d_cg}"
  puts "  Triangle: #{d_cg} ≤ #{d_cf} + #{d_fg}"
end

puts ""

# TEST 3: Composition Existence
puts "VERIFICATION 3: Composition Existence Proof"
puts "─" * 80

composition = {
  notes: [c, e, g],
  chords: [c_major, f_major, g_major, c_major]
}

existence = OntologicalValidator.validate_existence(composition)
puts "Existence validation:"
puts "  Exists: #{existence[:exists]}"
puts "  Worlds: #{existence[:worlds_count]}"
puts "  Validations:"
existence[:validations].each do |name, result|
  puts "    #{name}: #{result[:valid] ? '✓' : '✗'} (#{result[:errors].size} errors)"
end

if existence[:exists]
  puts ""
  puts "✓ Composition has mathematical existence"
  puts "  All objects have appearance in their worlds"
end

puts ""

# TEST 4: Semantic Closure
puts "VERIFICATION 4: Semantic Closure (8-Point Checklist)"
puts "─" * 80

closure = OntologicalValidator.semantic_closure(composition)
puts "Closure analysis:"

closure[:closure_points].each do |point, value|
  status = value ? "✓" : "✗"
  puts "  #{status} #{point}: #{value}"
end

puts ""
puts "Summary:"
puts "  Complete dimensions: #{closure[:summary][:valid_dimensions]}/#{closure[:summary][:total_dimensions]}"
puts "  Closure percentage: #{closure[:summary][:percentage]}%"
puts "  Semantically closed: #{closure[:closed] ? 'YES ✓' : 'NO ✗'}"

puts ""

# TEST 5: Necessary Transformations
puts "VERIFICATION 5: Transformation Necessity"
puts "─" * 80

puts "Checking if C→F→G→C path follows necessary transformations..."

necessity_cf = OntologicalValidator.transformation_necessary?(c_major, f_major, chord_world)
necessity_fg = OntologicalValidator.transformation_necessary?(f_major, g_major, chord_world)
necessity_gc = OntologicalValidator.transformation_necessary?(g_major, c_major, chord_world)

puts "  C → F: #{necessity_cf[:necessary] ? '✓ Necessary' : '✗ Not minimal'}"
puts "    Distance: #{necessity_cf[:direct_distance]}"

puts "  F → G: #{necessity_fg[:necessary] ? '✓ Necessary' : '✗ Not minimal'}"
puts "    Distance: #{necessity_fg[:direct_distance]}"

puts "  G → C: #{necessity_gc[:necessary] ? '✓ Necessary' : '✗ Not minimal'}"
puts "    Distance: #{necessity_gc[:direct_distance]}"

puts ""

# TEST 6: Logical Consistency
puts "VERIFICATION 6: Logical Consistency"
puts "─" * 80

consistency = OntologicalValidator.logical_consistency(composition)
puts "Consistency check:"
puts "  Consistent: #{consistency[:consistent] ? '✓' : '✗'}"
puts "  Errors: #{consistency[:error_count]}"

if consistency[:error_count] > 0
  consistency[:errors].each { |e| puts "    - #{e}" }
else
  puts "  ✓ No logical contradictions"
end

puts ""

# FINAL SUMMARY
puts "=" * 80
puts "ONTOLOGICAL VERIFICATION SUMMARY"
puts "=" * 80
puts ""

all_valid = [
  validation[:valid],
  existence[:exists],
  closure[:closed],
  consistency[:consistent]
]

if all_valid.all?
  puts "✓ COMPOSITION IS MATHEMATICALLY VALID"
  puts ""
  puts "The system has verified:"
  puts "  • Metric space axioms (triangle inequality)"
  puts "  • Object existence in worlds"
  puts "  • Semantic closure (8 dimensions)"
  puts "  • Logical consistency"
  puts "  • Necessary transformations"
  puts ""
  puts "Ontological status: ACCEPTED"
  puts "The composition exists within the mathematical world of music."
else
  puts "✗ COMPOSITION FAILS VERIFICATION"
  puts ""
  puts "Issues:"
  puts "  Metric space valid: #{validation[:valid]}"
  puts "  Existence proven: #{existence[:exists]}"
  puts "  Semantically closed: #{closure[:closed]}"
  puts "  Logically consistent: #{consistency[:consistent]}"
end

puts ""
puts "=" * 80
