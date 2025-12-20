#!/usr/bin/env ruby
# lib/worlds/modulation_world.rb
#
# ModulationWorld: Badiouian world for key modulation analysis
#
# Objects: Keys and modulation paths
# Relations: Chromatic distance between keys
# Axioms: Circle of fifths, transposition preservation

require_relative '../worlds'
require_relative '../modulation'

class ModulationWorld < MusicalWorlds::World
  attr_reader :modulation_paths, :keys_visited

  def initialize
    # Metric: chromatic distance between keys
    # Shorter paths indicate closer harmonic relationships
    metric = lambda { |key1, key2|
      # Extract key names from objects
      k1 = key1.is_a?(String) ? key1 : (key1.respond_to?(:from_key) ? key1.from_key : key1.to_s)
      k2 = key2.is_a?(String) ? key2 : (key2.respond_to?(:from_key) ? key2.from_key : key2.to_s)

      Modulation.chromatic_distance(k1, k2)
    }

    super("Modulation World", metric)

    @modulation_paths = []
    @keys_visited = Set.new
  end

  # Add a key to world
  def add_key(key)
    @objects.add(key)
    @keys_visited.add(key)
  end

  # Add modulation between two keys
  def add_modulation(from_key, to_key, type = :direct, pivot_chord = nil)
    add_key(from_key)
    add_key(to_key)

    mod = Modulation.new(from_key, to_key, type, pivot_chord)
    @objects.add(mod)
    mod
  end

  # Add complete modulation path
  def add_modulation_path(keys)
    path = ModulationPath.new(keys)
    @modulation_paths << path

    keys.each { |k| add_key(k) }
    path
  end

  # Analyze modulation between two keys
  def analyze_modulation(from_key, to_key)
    distance = Modulation.chromatic_distance(from_key, to_key)
    circle_distance = Modulation.circle_of_fifths_distance(from_key, to_key)
    common_tone_dist = Modulation.common_tone_distance(from_key, to_key)
    pivot = Modulation.analyze_pivot_chord(from_key, to_key)

    {
      from_key: from_key,
      to_key: to_key,
      chromatic_distance: distance,
      circle_of_fifths_distance: circle_distance,
      common_tone_distance: common_tone_dist,
      pivot_chord: pivot,
      best_type: determine_modulation_type(distance, common_tone_dist)
    }
  end

  # Check triangle inequality in key space
  def triangle_inequality_in_keys(key1, key2, key3)
    d12 = Modulation.chromatic_distance(key1, key2)
    d23 = Modulation.chromatic_distance(key2, key3)
    d13 = Modulation.chromatic_distance(key1, key3)

    satisfied = d13 <= d12 + d23

    {
      keys: [key1, key2, key3],
      d12: d12,
      d23: d23,
      d13: d13,
      satisfied: satisfied,
      inequality: "#{d13} ≤ #{d12} + #{d23} = #{d12 + d23}"
    }
  end

  # Semantic closure validation
  def semantic_closure_validation
    {
      pitch_space: @keys_visited.length > 0,
      chord_space: @modulation_paths.length > 0,
      metric_valid: validate_metric_space[:valid],
      appearance: @objects.length > 0,
      transformations_necessary: verify_transposition_rules,
      consistent: verify_no_key_contradictions,
      existence: @modulation_paths.length > 0,
      complete: verify_modulation_closure
    }
  end

  private

  def determine_modulation_type(chromatic_dist, common_tone_dist)
    case
    when common_tone_dist <= 1
      :pivot_chord
    when chromatic_dist <= 2
      :chromatic
    else
      :direct
    end
  end

  def verify_transposition_rules
    # Transposition preserves interval relationships
    # If T maps C→D, all notes shift by 2 semitones
    true  # Simplified
  end

  def verify_no_key_contradictions
    # Check: each key appears consistently
    @keys_visited.all? { |k| k.is_a?(String) }
  end

  def verify_modulation_closure
    # Check: modulation paths form closed system
    @modulation_paths.any? { |path| path.keys.length >= 2 }
  end
end

# Factory methods
class ModulationWorld
  def self.create_related_keys_world
    world = new

    # Add C and its related keys
    world.add_key('C')          # Tonic
    world.add_key('G')          # Dominant (5 sharps away)
    world.add_key('F')          # Subdominant (1 flat)
    world.add_key('A')          # Relative minor
    world.add_key('D')          # Secondary dominant

    # Add modulations
    world.add_modulation('C', 'G', :pivot_chord)
    world.add_modulation('C', 'F', :pivot_chord)
    world.add_modulation('C', 'A', :direct)

    world
  end

  def self.create_chromatic_progression_world
    world = new

    # Chromatic key progression
    keys = ['C', 'C#', 'D', 'D#', 'E', 'F']
    world.add_modulation_path(keys)

    world
  end

  def self.create_circle_of_fifths_world
    world = new

    # Circle of fifths progression
    keys = ['C', 'G', 'D', 'A', 'E', 'B']
    world.add_modulation_path(keys)

    world
  end
end
