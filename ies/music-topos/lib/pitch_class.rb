# lib/pitch_class.rb
require 'set'

class PitchClass
  SEMITONES = 12
  CHROMATIC_NOTES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']

  attr_reader :value

  def self.from_midi(midi_note)
    new(midi_note)
  end

  def self.from_name(name)
    # Normalize flats to sharps
    normalization = {
      'Cb' => 'B', 'Db' => 'C#', 'Eb' => 'D#', 'Fb' => 'E', 
      'Gb' => 'F#', 'Ab' => 'G#', 'Bb' => 'A#',
      'E#' => 'F', 'B#' => 'C'
    }
    normalized = normalization[name] || name
    index = CHROMATIC_NOTES.index(normalized)
    raise "Invalid note name: #{name}" unless index
    new(index)
  end

  def self.note_names
    CHROMATIC_NOTES
  end

  def initialize(value)
    @value = value % SEMITONES
  end

  def transpose(semitones)
    PitchClass.new(@value + semitones)
  end

  def distance(other)
    diff = (other.value - @value).abs
    [diff, SEMITONES - diff].min
  end

  def to_midi(octave = 4)
    (octave + 1) * 12 + @value
  end

  def to_frequency(octave = 4)
    440.0 * (2.0 ** ((to_midi(octave) - 69) / 12.0))
  end

  def note_name
    CHROMATIC_NOTES[@value]
  end

  def to_s
    "PitchClass(#{note_name})"
  end

  def inspect
    to_s
  end

  def ==(other)
    other.is_a?(PitchClass) && @value == other.value
  end

  def hash
    @value.hash
  end

  def +(other)
    val = other.is_a?(PitchClass) ? other.value : other
    transpose(val)
  end

  def -(other)
    val = other.is_a?(PitchClass) ? other.value : other
    transpose(-val)
  end
end
