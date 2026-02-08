# lib/progressions.rb
require_relative 'chord'
require_relative 'harmonic_function'

class HarmonicProgression
  COMMON_PROGRESSIONS = {
    tonic_prolongation: ['I', 'vi', 'IV', 'ii'],
    authentic_cadence:  ['V', 'I'],
    plagal_cadence:     ['IV', 'I'],
    full_cycle:         ['I', 'IV', 'V', 'I'],
    deceptive:          ['V', 'vi']
  }

  def self.analyze(chords, key)
    chords.map do |chord|
      HarmonicFunction.analyze(chord, key)
    end
  end

  def self.roman_numeral(chord, key)
    # Simplified Roman Numeral analysis
    root_pc = chord.root.value
    key_pc = PitchClass.from_name(key).value
    interval = (root_pc - key_pc) % 12
    
    case interval
    when 0 then 'I'
    when 2 then 'ii'
    when 4 then 'iii'
    when 5 then 'IV'
    when 7 then 'V'
    when 9 then 'vi'
    when 11 then 'vii°'
    else "b#{interval}" # fallback
    end
  end
end
