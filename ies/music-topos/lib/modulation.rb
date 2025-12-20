#!/usr/bin/env ruby
# lib/modulation.rb
#
# Category 6: Modulation & Transposition
#
# Modulation = change of key
# Transposition = shift all pitches by fixed interval
#
# Three types of modulation:
# 1. Pivot chord modulation (shared chord between keys)
# 2. Chromatic modulation (smooth voice leading)
# 3. Direct modulation (immediate key change)
#
# Distance metric: chromatic steps in modulation path

require 'set'
require_relative 'pitch_class'

class Modulation
  # Modulation types
  PIVOT_CHORD = :pivot_chord
  CHROMATIC = :chromatic
  DIRECT = :direct

  attr_reader :from_key, :to_key, :type, :pivot_chord, :path

  def initialize(from_key, to_key, type = :direct, pivot_chord = nil)
    @from_key = from_key
    @to_key = to_key
    @type = type
    @pivot_chord = pivot_chord
    @path = []
  end

  # Transposition: shift all pitches by interval
  # Returns new key (transposed)
  def self.transpose_key(key, semitones)
    # Simple key transposition
    # If key is 'C', semitones=2 → 'D'
    key_map = {
      'C' => 0, 'G' => 7, 'D' => 2, 'A' => 9, 'E' => 4, 'B' => 11,
      'F#' => 6, 'C#' => 1, 'G#' => 8, 'D#' => 3, 'A#' => 10, 'F' => 5,
      'Bb' => 10, 'Eb' => 3, 'Ab' => 8, 'Db' => 1, 'Gb' => 6, 'Cb' => 11
    }

    reverse_map = key_map.invert

    current_pitch = key_map[key] || 0
    new_pitch = (current_pitch + semitones) % 12
    reverse_map[new_pitch] || 'C'
  end

  # Chromatic distance between two keys
  # Shortest path in circle of fifths or chromatic scale
  def self.chromatic_distance(key1, key2)
    key_pitches = {
      'C' => 0, 'G' => 7, 'D' => 2, 'A' => 9, 'E' => 4, 'B' => 11,
      'F#' => 6, 'C#' => 1, 'G#' => 8, 'D#' => 3, 'A#' => 10, 'F' => 5,
      'Bb' => 10, 'Eb' => 3, 'Ab' => 8, 'Db' => 1, 'Gb' => 6, 'Cb' => 11
    }

    pitch1 = key_pitches[key1] || 0
    pitch2 = key_pitches[key2] || 0

    # Chromatic distance (shortest path on circle)
    diff = (pitch2 - pitch1).abs
    [diff, 12 - diff].min
  end

  # Circle of fifths distance (more musical)
  def self.circle_of_fifths_distance(key1, key2)
    # In circle of fifths: C - G - D - A - E - B - F# - C# - G# - D# - A# - F - C
    circle = ['C', 'G', 'D', 'A', 'E', 'B', 'F#', 'C#', 'G#', 'D#', 'A#', 'F']

    idx1 = circle.index(key1) || 0
    idx2 = circle.index(key2) || 0

    diff = (idx2 - idx1).abs
    [diff, 12 - diff].min
  end

  # Common tone modulation: keys sharing pitches
  # In C Major: C E G
  # In A minor: A C E (shares C and E)
  def self.common_tone_distance(key1, key2)
    # Simplified: assume major triads
    # C Major triad: C E G (0, 4, 7)
    # F Major triad: F A C (5, 9, 0)
    # Shared notes: C → distance 2

    triads = {
      'C' => Set.new([0, 4, 7]),
      'G' => Set.new([7, 11, 2]),
      'D' => Set.new([2, 6, 9]),
      'A' => Set.new([9, 1, 4]),
      'E' => Set.new([4, 8, 11]),
      'B' => Set.new([11, 3, 7]),
      'F' => Set.new([5, 9, 0]),
      'Bb' => Set.new([10, 2, 5]),
      'Eb' => Set.new([3, 7, 10]),
      'Ab' => Set.new([8, 0, 5]),
      'Db' => Set.new([1, 5, 8]),
      'F#' => Set.new([6, 10, 1])
    }

    notes1 = triads[key1] || Set.new
    notes2 = triads[key2] || Set.new

    common = notes1 & notes2
    return 0 if common.size == 3  # Identical keys
    return 1 if common.size == 2  # One note shared
    return 2 if common.size == 1  # One note shared
    return 3  # No shared notes (chromatic leap)
  end

  # Pivot chord modulation analysis
  def self.analyze_pivot_chord(from_key, to_key)
    # Find chord that functions in both keys
    # Example: C Major and A minor share C Major (I in C, III in A minor)

    from_triads = {
      'C' => ['C Major', 'D minor', 'E minor', 'F Major', 'G Major', 'A minor', 'B dim'],
      'A' => ['A minor', 'B dim', 'C Major', 'D minor', 'E minor', 'F Major', 'G Major']
    }

    # Simplified: just check if keys share scale degrees
    # Real implementation would need full harmonic analysis

    shared = from_triads[from_key] & from_triads[to_key] rescue []
    shared.first if shared.any?
  end

  def to_s
    "Modulation(#{@from_key} → #{@to_key}, #{@type})"
  end

  def ==(other)
    other.is_a?(Modulation) &&
      @from_key == other.from_key &&
      @to_key == other.to_key &&
      @type == other.type
  end

  def hash
    [@from_key, @to_key, @type].hash
  end
end

# Transposition: shift pitch by interval
class Transposition
  attr_reader :semitones, :direction

  def initialize(semitones)
    @semitones = semitones % 12
    @direction = semitones >= 0 ? :up : :down
  end

  # Apply transposition to pitch class
  def apply(pitch_class)
    PitchClass.new(pitch_class.value + @semitones)
  end

  # Apply to chord
  def apply_to_chord(chord)
    Chord.new(*chord.voices.map { |v| apply(v) })
  end

  def to_s
    direction = @direction == :up ? '+' : '-'
    "T#{direction}#{@semitones.abs}"
  end

  def ==(other)
    other.is_a?(Transposition) && @semitones == other.semitones
  end

  def hash
    @semitones.hash
  end
end

# Modulation path: sequence of keys
class ModulationPath
  attr_reader :keys, :modulations

  def initialize(keys = [])
    @keys = keys
    @modulations = []

    # Calculate modulations between consecutive keys
    (1...keys.length).each do |i|
      mod = Modulation.new(keys[i-1], keys[i], :direct)
      @modulations << mod
    end
  end

  # Add key to path
  def add_key(key)
    if @keys.any?
      mod = Modulation.new(@keys.last, key, :direct)
      @modulations << mod
    end
    @keys << key
  end

  # Total distance in modulation path
  def total_distance
    @modulations.sum { |m| Modulation.chromatic_distance(m.from_key, m.to_key) }
  end

  # Does path return to original key?
  def returns_to_origin?
    @keys.first == @keys.last if @keys.length > 1
  end

  def to_s
    "ModulationPath(#{@keys.join(' → ')})"
  end
end
