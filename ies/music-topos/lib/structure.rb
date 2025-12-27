# lib/structure.rb
require_relative 'progressions'

class Cadence
  TYPES = [:authentic, :plagal, :half, :deceptive, :none]

  def self.detect(chords, key)
    return :none if chords.size < 2
    last = HarmonicProgression.roman_numeral(chords[-1], key)
    prev = HarmonicProgression.roman_numeral(chords[-2], key)
    
    if last == 'I'
      return :authentic if prev == 'V' || prev == 'vii°'
      return :plagal if prev == 'IV'
    elsif last == 'V'
      return :half
    elsif last == 'vi' && prev == 'V'
      return :deceptive
    end
    
    :none
  end
end

class Phrase
  attr_reader :chords, :cadence

  def initialize(chords, key)
    @chords = chords
    @cadence = Cadence.detect(chords, key)
  end

  def antecedent?
    @cadence == :half
  end

  def consequent?
    @cadence == :authentic || @cadence == :plagal
  end
end
