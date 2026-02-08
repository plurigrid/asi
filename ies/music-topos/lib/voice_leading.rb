# lib/voice_leading.rb
require_relative 'chord'

class VoiceLeading
  # SATB Range Constraints (MIDI notes)
  RANGES = {
    soprano: (60..81), # C4 to A5
    alto:    (55..74), # G3 to D5
    tenor:   (48..69), # C3 to A4
    bass:    (40..60)  # E2 to C4
  }

  def self.validate_satb(chord, octaves)
    errors = []
    
    # Check voice counts
    unless chord.voices.size == 4
      errors << "SATB requires exactly 4 voices (found #{chord.voices.size})"
      return errors
    end

    # Check ranges
    midi_notes = chord.to_midi_notes(octaves)
    voice_names = [:soprano, :alto, :tenor, :bass]
    
    midi_notes.each_with_index do |note, idx|
      voice = voice_names[idx]
      range = RANGES[voice]
      unless range.include?(note)
        errors << "#{voice.to_s.capitalize} out of range: #{note} (allowed: #{range})"
      end
    end

    # Check for crossing voices
    # Soprano > Alto > Tenor > Bass
    (0..2).each do |i|
      if midi_notes[i] < midi_notes[i+1]
        errors << "Voice crossing detected: #{voice_names[i]} (#{midi_notes[i]}) below #{voice_names[i+1]} (#{midi_notes[i+1]})"
      end
    end

    errors
  end

  def self.check_parallels(chord1, octaves1, chord2, octaves2)
    errors = []
    m1 = chord1.to_midi_notes(octaves1)
    m2 = chord2.to_midi_notes(octaves2)

    # Check all pairs of voices for parallel 5ths and 8ves
    (0..3).to_a.combination(2).each do |v1, v2|
      interval1 = (m1[v1] - m1[v2]).abs % 12
      interval2 = (m2[v1] - m2[v2]).abs % 12
      
      # Motion
      motion1 = m2[v1] - m1[v1]
      motion2 = m2[v2] - m1[v2]
      
      if motion1 != 0 && motion1 == motion2 # Parallel motion
        if interval2 == 7 # Perfect 5th
          errors << "Parallel 5ths between voices #{v1} and #{v2}" if interval1 == 7
        elsif interval2 == 0 # Octave
          errors << "Parallel octaves between voices #{v1} and #{v2}" if interval1 == 0
        end
      end
    end
    
    errors
  end
  
  def self.smoothness_analysis(chord1, octaves1, chord2, octaves2)
    m1 = chord1.to_midi_notes(octaves1)
    m2 = chord2.to_midi_notes(octaves2)
    
    motions = m1.zip(m2).map { |n1, n2| (n2 - n1).abs }
    total_motion = motions.sum
    
    {
      total_motion: total_motion,
      average_motion: total_motion / 4.0,
      max_jump: motions.max,
      is_smooth: motions.max <= 4 # No jump larger than a major 3rd
    }
  end
end
