#!/usr/bin/env ruby
# lib/harmonic_function.rb
#
# Harmonic Function Analysis for Music Topos Category 5
#
# Musical chords have functional roles in harmonic space:
# - T (Tonic): stability, resolution point, home
# - S (Subdominant): movement, preparation, moving away
# - D (Dominant): tension, pull, drive toward resolution
#
# Functions form a closed cycle: T → S → D → T
# Distance metric: valid progressions have distance 1,
#                  unusual progressions have distance > 1

require 'set'
require_relative 'pitch_class'
require_relative 'chord'

class HarmonicFunction
  # Three fundamental harmonic functions
  TONIC = :tonic
  SUBDOMINANT = :subdominant
  DOMINANT = :dominant

  # All functions as set
  FUNCTIONS = Set.new([TONIC, SUBDOMINANT, DOMINANT])

  attr_reader :function, :chord, :key

  def initialize(chord, function, key = nil)
    raise "Invalid function: #{function}" unless FUNCTIONS.include?(function)

    @chord = chord
    @function = function
    @key = key  # Optional: key context
  end

  # Create from chord root and context
  def self.from_chord(chord, key_context = 'C')
    root = chord.root
    function = analyze_function(root, key_context)
    new(chord, function, key_context)
  end

  # Analyze which function a chord has based on root
  # In C Major: C=T, D=S, E=S, F=S, G=D, A=S, B=D
  def self.analyze_function(root_pitch, key = 'C')
    # Assume root_pitch is a PitchClass or integer (0-11)
    pitch_value = root_pitch.is_a?(PitchClass) ? root_pitch.value : root_pitch

    # Get key root
    key_root = case key.upcase
               when 'C' then 0
               when 'G' then 7
               when 'D' then 2
               when 'A' then 9
               when 'E' then 4
               when 'B' then 11
               when 'F' then 5
               when 'BB' then 10
               when 'EB' then 3
               when 'AB' then 8
               else 0  # Default to C
               end

    # Distance from key root
    distance = (pitch_value - key_root) % 12

    # Roman numeral analysis in major key
    # I(T)  ii(S) iii(S) IV(S) V(D) vi(S) vii°(D)
    case distance
    when 0 then TONIC         # I (0)
    when 2 then SUBDOMINANT   # ii (2)
    when 4 then SUBDOMINANT   # iii (4)
    when 5 then SUBDOMINANT   # IV (5)
    when 7 then DOMINANT      # V (7)
    when 9 then SUBDOMINANT   # vi (9)
    when 11 then DOMINANT     # vii° (11)
    else SUBDOMINANT          # Default to S
    end
  end

  # Distance in functional space
  # Valid progressions (T→S, S→D, D→T) have distance 1
  # Other progressions have higher distance
  def distance_to(other_function)
    return 0 if @function == other_function

    # Define valid transitions and their distances
    # All valid: T→S→D→T forms a directed cycle
    transitions = {
      # From Tonic
      [TONIC, SUBDOMINANT] => 1,
      [TONIC, DOMINANT] => 2,      # Not typical without S
      # From Subdominant
      [SUBDOMINANT, DOMINANT] => 1,
      [SUBDOMINANT, TONIC] => 2,   # Not typical without D
      # From Dominant
      [DOMINANT, TONIC] => 1,
      [DOMINANT, SUBDOMINANT] => 2, # Not typical (goes backwards)
    }

    key = [@function, other_function]
    transitions[key] || 3  # Unknown transition = distance 3
  end

  # Check if progression T₁ → T₂ is valid (distance = 1)
  def self.valid_progression?(func1, func2)
    new(nil, func1).distance_to(func2) == 1
  end

  # Cadences are terminal progressions
  # Authentic: V → I (dominant → tonic)
  # Plagal: IV → I (subdominant → tonic)
  # Deceptive: V → vi (dominant → vi, broken expectation)
  # Half: ? → V (anything → dominant, unresolved)
  def self.cadence_type(func1, func2)
    case [func1, func2]
    when [DOMINANT, TONIC]
      :authentic
    when [SUBDOMINANT, TONIC]
      :plagal
    when [DOMINANT, :vi]
      :deceptive
    when [nil, DOMINANT], [:any, DOMINANT]
      :half
    else
      :other
    end
  end

  # Functional closure: verify all functions present in progression
  def self.functional_closure(chord_sequence)
    functions = chord_sequence.map { |chord| from_chord(chord).function }

    # Check if all three functions appear
    has_tonic = functions.include?(TONIC)
    has_subdominant = functions.include?(SUBDOMINANT)
    has_dominant = functions.include?(DOMINANT)

    {
      has_tonic: has_tonic,
      has_subdominant: has_subdominant,
      has_dominant: has_dominant,
      complete: has_tonic && has_subdominant && has_dominant,
      functions_present: functions.uniq.length,
      cycle_complete: has_tonic && has_dominant  # Minimal requirement
    }
  end

  # =========================================================================
  # Color-Based Harmonic Function Analysis
  # Maps LCH color hue zones to harmonic functions
  # =========================================================================

  # Analyze harmonic function from color (primarily hue)
  # Hue zones map to T/S/D functional harmony:
  # T (Tonic):      330-90°  (reds, warm, stable)
  # S (Subdominant): 90-210° (greens, cool, motion)
  # D (Dominant):   210-330° (blues, active, tension)
  def self.color_to_function(color)
    # Extract hue from color (Hash or object with .H accessor)
    hue = case color
           when Hash
             color[:H] || color['H'] || 0
           else
             color.H || 0
           end

    # Map hue to functional zone
    case hue
    when 330...360, 0...90     # Red-orange: Tonic (home)
      TONIC
    when 90...210              # Green-cyan: Subdominant (motion)
      SUBDOMINANT
    when 210...330             # Blue-purple: Dominant (tension)
      DOMINANT
    else
      TONIC  # Default fallback
    end
  end

  # Analyze a sequence of colors and return functional progression
  def self.color_sequence_analysis(colors)
    functions = colors.map { |color| color_to_function(color) }
    closure = functional_closure_from_functions(functions)

    {
      functions: functions,
      closure: closure,
      has_authentic_cadence: functions.length >= 2 && functions[-2] == DOMINANT && functions[-1] == TONIC,
      has_plagal_cadence: functions.length >= 2 && functions[-2] == SUBDOMINANT && functions[-1] == TONIC,
      progression_type: classify_progression(functions)
    }
  end

  private

  def self.functional_closure_from_functions(functions)
    has_tonic = functions.include?(TONIC)
    has_subdominant = functions.include?(SUBDOMINANT)
    has_dominant = functions.include?(DOMINANT)

    {
      complete: has_tonic && has_subdominant && has_dominant,
      tonic: has_tonic,
      subdominant: has_subdominant,
      dominant: has_dominant,
      function_count: functions.uniq.length
    }
  end

  def self.classify_progression(functions)
    # Classify based on function pattern
    if functions.length < 2
      :single
    elsif functions[-2] == DOMINANT && functions[-1] == TONIC
      :authentic_cadence
    elsif functions[-2] == SUBDOMINANT && functions[-1] == TONIC
      :plagal_cadence
    elsif functions[-2] == DOMINANT && functions[-1] == SUBDOMINANT
      :deceptive_cadence
    elsif functions.uniq.length == 1
      :static
    else
      :dynamic
    end
  end

  def to_s
    "#{chord}(#{@function.to_s.upcase[0]})"
  end

  def ==(other)
    other.is_a?(HarmonicFunction) &&
      @function == other.function &&
      @chord == other.chord
  end

  def hash
    [@function, @chord].hash
  end
end

# Functional chord with harmonic context
class FunctionalChord
  attr_reader :chord, :function, :position, :inversion

  def initialize(chord, function, position = 1, inversion = 0)
    @chord = chord
    @function = function
    @position = position  # Position in progression
    @inversion = inversion  # 0=root, 1=first, 2=second
  end

  # Create from roman numeral (I, IV, V, vi, etc.)
  def self.from_roman(numeral, key = 'C')
    # Parse roman numeral and create chord
    # I → major triad on key root
    # IV → major triad on subdominant
    # V → major triad on dominant
    # vi → minor triad on submediant
    # etc.
    function = HarmonicFunction.analyze_function(0, key)  # Placeholder
    new(nil, function)
  end

  def to_s
    "#{@chord}(#{@function.to_s[0].upcase}#{@inversion})"
  end
end
