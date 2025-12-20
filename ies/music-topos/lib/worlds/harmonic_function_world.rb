#!/usr/bin/env ruby
# lib/worlds/harmonic_function_world.rb
#
# HarmonicFunctionWorld: Badiouian world for harmonic function analysis
#
# Objects: Harmonic functions (T, S, D)
# Relations: Valid progressions (T→S→D→T cycle)
# Axioms: Functional closure, valid transitions, cadential rules

require_relative '../worlds'
require_relative '../harmonic_function'

class HarmonicFunctionWorld < MusicalWorlds::World
  attr_reader :key, :progressions

  def initialize(key = 'C')
    @key = key

    # Metric: functional distance
    # Valid progressions (distance 1): T→S, S→D, D→T
    # Deceptive progressions (distance 2): avoid cycles
    # Invalid progressions (distance 3): backwards motion
    metric = lambda { |func1, func2|
      if func1.is_a?(HarmonicFunction)
        func1.distance_to(func2.function)
      else
        # func1, func2 are function symbols
        distance_between_functions(func1, func2)
      end
    }

    super("Harmonic Function World (#{key})", metric)

    @progressions = []
  end

  # Add a functional chord to the world
  def add_functional_chord(chord, function_symbol = nil)
    # Get root from first voice (bass note in SATB)
    root = chord.voices.first.value rescue 0
    function_symbol ||= HarmonicFunction.analyze_function(root, @key)
    hf = HarmonicFunction.new(chord, function_symbol, @key)

    @objects.add(hf)
    hf
  end

  # Add a chord progression
  def add_progression(chord_sequence)
    functional_chord_sequence = chord_sequence.map do |chord|
      add_functional_chord(chord)
    end

    @progressions << functional_chord_sequence
    functional_chord_sequence
  end

  # Validate functional progression rules
  def validate_progression(chord_sequence)
    errors = []

    chord_sequence.each_with_index do |chord, idx|
      next if idx == 0

      prev_chord = chord_sequence[idx - 1]
      func_curr = HarmonicFunction.from_chord(chord, @key)
      func_prev = HarmonicFunction.from_chord(prev_chord, @key)

      # Check if transition is valid
      distance = func_prev.distance_to(func_curr.function)

      if distance > 1
        errors << "Unusual transition at #{idx}: #{func_prev.function} → #{func_curr.function} (distance #{distance})"
      end
    end

    {
      valid: errors.empty?,
      errors: errors,
      chord_count: chord_sequence.length,
      unusuality_level: errors.length  # How many unusual transitions
    }
  end

  # Analyze cadence at end of progression
  def analyze_cadence(chord_sequence)
    return nil if chord_sequence.length < 2

    second_last = chord_sequence[-2]
    last = chord_sequence[-1]

    func_penultimate = HarmonicFunction.from_chord(second_last, @key)
    func_final = HarmonicFunction.from_chord(last, @key)

    {
      penultimate_function: func_penultimate.function,
      final_function: func_final.function,
      cadence_type: HarmonicFunction.cadence_type(
        func_penultimate.function,
        func_final.function
      ),
      resolves_to_tonic: func_final.function == HarmonicFunction::TONIC
    }
  end

  # Functional closure validation (8-dimension requirement)
  def semantic_closure_validation
    {
      pitch_space: @progressions.all? { |seq| seq.all? { |fc| fc.chord.valid? } },
      chord_space: @progressions.all? { |seq| seq.length >= 2 },
      metric_valid: validate_metric_space[:valid],
      appearance: @objects.length > 0,
      transformations_necessary: verify_functional_rules,
      consistent: verify_no_contradictions,
      existence: @progressions.length > 0,
      complete: verify_closure
    }
  end

  # Verify all functional rules are satisfied
  def verify_functional_rules
    return true if @progressions.empty?

    @progressions.all? do |progression|
      validation = validate_progression(progression.map(&:chord))
      validation[:valid] || validation[:errors].length <= 1  # Allow at most one unusual transition
    end
  end

  # Verify no contradictions in functional analysis
  def verify_no_contradictions
    # Check: chord root should map to only one function in given key
    root_to_function = {}

    @objects.each do |hf|
      root = hf.chord.root
      if root_to_function[root] && root_to_function[root] != hf.function
        return false  # Contradiction: root maps to different functions
      end

      root_to_function[root] = hf.function
    end

    true
  end

  # Verify functional closure: progressions form closed harmonic system
  def verify_closure
    return false if @progressions.empty?

    @progressions.all? do |progression|
      closure = HarmonicFunction.functional_closure(progression.map(&:chord))
      closure[:cycle_complete]  # At least T and D present
    end
  end

  # Harmonic rhythm: analyze timing of functional changes
  def harmonic_rhythm(chord_sequence)
    functions = chord_sequence.map do |chord|
      HarmonicFunction.from_chord(chord, @key).function
    end

    # Count function changes
    changes = 0
    (1...functions.length).each do |i|
      changes += 1 if functions[i] != functions[i - 1]
    end

    {
      total_chords: chord_sequence.length,
      function_changes: changes,
      harmonic_rhythm_ratio: changes.to_f / chord_sequence.length,
      functions_used: functions.uniq.length,
      cadence: analyze_cadence(chord_sequence)
    }
  end

  private

  def distance_between_functions(func1, func2)
    case [func1, func2]
    when [HarmonicFunction::TONIC, HarmonicFunction::SUBDOMINANT]
      1
    when [HarmonicFunction::SUBDOMINANT, HarmonicFunction::DOMINANT]
      1
    when [HarmonicFunction::DOMINANT, HarmonicFunction::TONIC]
      1
    else
      2  # Non-primary transition
    end
  end
end

# Factory methods
class HarmonicFunctionWorld
  # Create world with common progressions
  def self.create_with_common_progressions(key = 'C')
    world = new(key)

    # I-IV-V-I (Common, opens with authentic cadence)
    progression1 = [
      Chord.from_notes([key, (key.upcase[0].chr.succ + 'Maj3').to_sym],  1),
      Chord.from_notes([key, 'F'],                                      1),
      Chord.from_notes([key, 'G'],                                      1),
      Chord.from_notes([key, key.upcase[0].to_sym],                    1)
    ]

    # I-IV-I (Plagal, simpler)
    progression2 = [
      Chord.from_notes([key]),
      Chord.from_notes([key, 'F']),
      Chord.from_notes([key])
    ]

    world.add_progression(progression1) rescue nil  # Fallback if chord creation fails
    world.add_progression(progression2) rescue nil

    world
  end

  # Create world for harmonic analysis training
  def self.create_analysis_world(key = 'C')
    world = new(key)

    # Basic triads in key
    # This is simplified - would need full chord library
    triad_chords = [
      key,        # I (T)
      'ii',       # ii (S)
      'IV',       # IV (S)
      'V',        # V (D)
      'vi'        # vi (S)
    ]

    world
  end
end
