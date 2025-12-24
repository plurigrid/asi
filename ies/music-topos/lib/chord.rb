# lib/chord.rb
require_relative 'pitch_class'

class Chord
  attr_reader :voices

  def initialize(*voices)
    @voices = voices
  end

  def self.from_notes(note_names)
    voices = note_names.map do |name|
      PitchClass.from_name(name)
    end
    new(*voices)
  end

  def self.from_pitch_classes(pitches, voicing: :satb)
    new(*pitches)
  end

  def self.major_triad(root_pc)
    new(root_pc, root_pc + 4, root_pc + 7)
  end

  def self.minor_triad(root_pc)
    new(root_pc, root_pc + 3, root_pc + 7)
  end

  def self.diminished_triad(root_pc)
    new(root_pc, root_pc + 3, root_pc + 6)
  end

  def self.augmented_triad(root_pc)
    new(root_pc, root_pc + 4, root_pc + 8)
  end

  def voice_leading_distance(other)
    return Float::INFINITY if @voices.size != other.voices.size
    
    total = 0
    movements = []
    
    @voices.zip(other.voices).each do |v1, v2|
      dist = v1.distance(v2)
      total += dist
      movements << dist
    end
    
    {
      total: total,
      movements: movements,
      parsimonious: total < 6
    }
  end

  def smoothness_score(other)
    dist = voice_leading_distance(other)[:total]
    score = 1.0 / (1.0 + dist)
    {
      score: score,
      parsimonious: dist < 6,
      metric: dist
    }
  end

  def to_midi_notes(octaves)
    @voices.zip(octaves).map { |pc, oct| pc.to_midi(oct) }
  end

  def to_frequencies(octaves)
    @voices.zip(octaves).map { |pc, oct| pc.to_frequency(oct) }
  end

  def root
    @voices.first # Simplification
  end

  def soprano
    @voices[0]
  end

  def alto
    @voices[1]
  end

  def tenor
    @voices[2]
  end

  def bass
    @voices[3]
  end
  
  def to_s
    "Chord(#{@voices.map(&:note_name).join('-')})"
  end

  def inspect
    to_s
  end

  def ==(other)
    other.is_a?(Chord) && @voices == other.voices
  end

  def to_h
    {
      type: 'chord',
      voices: @voices.map(&:value)
    }
  end
end
