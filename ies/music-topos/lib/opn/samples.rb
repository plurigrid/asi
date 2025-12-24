# lib/opn/samples.rb
# OPN Component 11: Sample Manipulation
# Inspired by: Replica, Memory Vague

module OPN
  module Samples
    # Reverse simulation
    def self.reverse(events)
      return events if events.empty?
      
      max_time = events.map { |e| e[:at] + (e[:dur] || 0) }.max
      
      events.map do |e|
        new_time = max_time - e[:at] - (e[:dur] || 0)
        e.merge(at: [new_time, 0].max)
      end.sort_by { |e| e[:at] }
    end
    
    # Time stretch
    def self.time_stretch(events, factor: 2.0)
      events.map do |e|
        e.merge(
          at: e[:at] * factor,
          dur: (e[:dur] || 0.5) * factor
        )
      end
    end
    
    # Pitch shift (independent of time)
    def self.pitch_shift(events, semitones:)
      events.map do |e|
        e.merge(pitch: (e[:pitch] + semitones).clamp(24, 96))
      end
    end
    
    # Granular time stretch
    def self.granular_stretch(events, factor: 4.0, grain_size: 0.05)
      result = []
      
      events.each do |e|
        grains = ((e[:dur] || 0.5) * factor / grain_size).to_i
        
        grains.times do |g|
          result << {
            at: e[:at] * factor + g * grain_size,
            pitch: e[:pitch] + (rand - 0.5) * 0.5,
            dur: grain_size * 1.2,
            amp: e[:amp] * (0.8 + rand * 0.4)
          }
        end
      end
      
      result
    end
    
    # Formant shift (simulated)
    def self.formant_shift(events, shift: 5)
      events.map do |e|
        # Add formant-like harmonics
        [e] + [1.5, 2.5, 3.5].map do |ratio|
          {
            at: e[:at],
            pitch: (e[:pitch] + 12 * Math.log2(ratio) + shift).round.clamp(24, 96),
            dur: e[:dur],
            amp: e[:amp] * 0.2 / ratio
          }
        end
      end.flatten
    end
    
    # Paulstretch-like smear
    def self.paulstretch(events, stretch: 8.0, density: 20)
      result = []
      
      events.each do |e|
        duration = (e[:dur] || 0.5) * stretch
        grains = (density * duration).to_i
        
        grains.times do
          result << {
            at: e[:at] * stretch + rand * duration,
            pitch: e[:pitch] + (rand - 0.5),
            dur: duration / density * 2,
            amp: e[:amp] * 0.3
          }
        end
      end
      
      result.sort_by { |e| e[:at] }
    end
  end
end
