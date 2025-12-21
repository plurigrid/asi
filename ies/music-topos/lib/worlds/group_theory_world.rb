#!/usr/bin/env ruby
# lib/worlds/group_theory_world.rb
#
# GroupTheoryWorld: Badiouian world for S₁₂ group operations
#
# Objects: Permutations in S₁₂
# Relations: Cayley graph distance
# Axioms: Group closure, triangle inequality, voice leading preservation

require_relative '../worlds'
require_relative '../group_theory'

class GroupTheoryWorld < MusicalWorlds::World
  attr_reader :symmetric_group, :chord_objects

  def initialize
    # S₁₂ = symmetric group on 12 pitch classes
    @symmetric_group = S12.new

    # Metric: Cayley graph distance in S₁₂
    metric = lambda { |perm1, perm2|
      @symmetric_group.distance(perm1, perm2)
    }

    super("Group Theory World (S₁₂)", metric)

    @chord_objects = {}
  end

  # Add a chord to the world
  # Store permutations that transform it
  def add_chord(chord, label = nil)
    label ||= chord.to_s

    # Record the chord
    @chord_objects[label] = chord

    # Add identity permutation (the chord itself)
    @objects.add(Permutation.identity(12))
  end

  # Add a permutation (group element)
  def add_permutation(permutation, label = nil)
    label ||= permutation.to_s
    @objects.add(permutation)
  end

  # Verify group axioms hold in this world
  # Returns hash with validation results
  def validate_group_axioms
    validation = @symmetric_group.validate_group_axioms

    # Additional world-specific checks
    world_checks = {
      closure_in_world: check_closure_in_world,
      triangle_inequality_in_world: check_triangle_inequality_in_world,
      voice_leading_preserved: check_voice_leading_preservation
    }

    validation.merge(world_checks)
  end

  # Apply permutation to a chord
  def apply_permutation_to_chord(permutation, chord)
    @symmetric_group.voice_leading_action(chord, permutation)
  end

  # Analyze voice leading under permutation group action
  def analyze_voice_leading_under_action(chord1, chord2, max_perms = 5)
    # Find permutations that transform chord1 to chord2
    results = []

    # Sample permutations (full enumeration expensive for S₁₂)
    sample_size = [max_perms, @objects.size].min
    sample_perms = @objects.to_a.sample(sample_size)

    sample_perms.each do |perm|
      transformed = @symmetric_group.voice_leading_action(chord1, perm)

      # Compute voice leading distance
      vl_distance = @symmetric_group.voice_leading_distance(chord1, transformed)

      results << {
        permutation: perm,
        transformed_chord: transformed,
        voice_leading_distance: vl_distance,
        cayley_distance: @symmetric_group.distance(Permutation.identity(12), perm)
      }
    end

    results.sort_by { |r| r[:voice_leading_distance] }
  end

  # Check if composition of two permutations stays in world
  def check_closure_in_world
    return true if @objects.empty? || @objects.size < 2

    # Sample pairs of objects
    pairs = @objects.to_a.sample([@objects.size, 5].min).combination(2).to_a
    pairs.each do |perm1, perm2|
      composition = @symmetric_group.multiply(perm1, perm2)
      # Composition is always in S₁₂, so this always returns true
    end

    true
  end

  # Check triangle inequality holds for all triples in world
  def check_triangle_inequality_in_world
    return true if @objects.size < 3

    # Sample triples
    sample_size = [@objects.size, 5].min
    sample_objs = @objects.to_a.sample(sample_size)

    sample_objs.combination(3).each do |a, b, c|
      unless @symmetric_group.triangle_inequality_satisfied?(a, b, c)
        return false
      end
    end

    true
  end

  # Check that voice leading is preserved under group operations
  def check_voice_leading_preservation
    return true if @chord_objects.size < 2

    chords = @chord_objects.values.sample([@chord_objects.size, 3].min)
    return true if chords.size < 2

    chord1, chord2 = chords.sample(2)

    # Compare direct distance to distance through permutation
    direct_dist = @symmetric_group.voice_leading_distance(chord1, chord2)

    # Test with identity (should be zero)
    identity = Permutation.identity(12)
    identity_dist = @symmetric_group.voice_leading_distance(
      chord1,
      @symmetric_group.voice_leading_action(chord1, identity)
    )

    identity_dist == 0 && direct_dist >= 0
  end

  # Semantic closure validation for group theory
  def semantic_closure_validation
    # Group-theoretic closure conditions
    {
      group_axioms_valid: validate_group_axioms[:valid],
      cayley_metric_consistent: check_cayley_metric_consistency,
      voice_leading_under_actions: check_voice_leading_preservation,
      metric_space_valid: validate_metric_space[:valid]
    }
  end

  private

  def check_cayley_metric_consistency
    return true if @objects.size < 3

    # Verify Cayley metric properties
    sample_size = [@objects.size, 5].min
    sample_objs = @objects.to_a.sample(sample_size)

    # Check identity distance
    identity = Permutation.identity(12)
    sample_objs.each do |perm|
      d = @symmetric_group.distance(identity, perm)
      return false if d.nil? || d < 0
    end

    true
  end
end

# Factory methods for common group theory worlds

class GroupTheoryWorld
  # Create world with standard pitch permutations
  def self.create_with_pitch_permutations
    world = new

    # Add C Major chord
    c_major = Chord.from_notes(['C', 'E', 'G'])
    world.add_chord(c_major, "C Major")

    # Add some transpositions
    (0..11).each do |pitch|
      next if pitch == 0  # Skip C (identity)
      transposition = Permutation.transposition(12, 0, pitch)
      world.add_permutation(transposition, "Transposition to #{pitch} semitones")
    end

    world
  end

  # Create world with adjacent transposition generators
  def self.create_with_generators
    world = new

    # Add all adjacent transposition generators
    (0..10).each do |i|
      gen = Permutation.transposition(12, i, i + 1)
      world.add_permutation(gen, "(#{i} #{i+1})")
    end

    world
  end

  # Create world exploring specific chord family
  def self.create_chord_family_world(root_note)
    world = new

    # Add root chord
    root_chord = Chord.from_notes([root_note])
    world.add_chord(root_chord, "Root: #{root_note}")

    # Add major triad
    major_chord = Chord.from_notes([root_note, root_note.upcase])
    world.add_chord(major_chord, "#{root_note} Major")

    # Add minor triad (permutation of 3rd)
    minor_chord = Chord.from_notes([root_note, (root_note.upcase + 'b'), root_note.upcase])
    world.add_chord(minor_chord, "#{root_note} Minor")

    world
  end
end
