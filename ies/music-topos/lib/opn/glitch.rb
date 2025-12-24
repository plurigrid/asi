# lib/opn/glitch.rb
# OPN Component 7: Glitch Interruptions
# Inspired by: Replica, Problem Areas

module OPN
  module Glitch
    # Buffer stutter
    def self.buffer_stutter(pitch, buffer_size: 0.05, repeats: 16)
      events = []
      
      repeats.times do |i|
        events << {
          at: i * buffer_size,
          pitch: pitch + (rand > 0.8 ? rand(-12..12) : 0),
          dur: buffer_size * 0.9,
          amp: 0.4 * (1 - i * 0.03)
        }
      end
      
      events
    end
    
    # Bitcrush simulation (pitch quantization)
    def self.bitcrush(events, bits: 4)
      step = 12.0 / (2 ** bits)
      
      events.map do |e|
        crushed_pitch = (e[:pitch] / step).round * step
        e.merge(pitch: crushed_pitch.round)
      end
    end
    
    # CD skip effect
    def self.cd_skip(pattern, skip_probability: 0.2)
      events = []
      time = 0
      
      pattern.each do |e|
        if rand < skip_probability
          # Skip and repeat previous
          3.times do |r|
            events << {
              at: time + r * 0.05,
              pitch: e[:pitch],
              dur: 0.04,
              amp: e[:amp] * 0.8
            }
          end
        else
          events << e.merge(at: time)
        end
        
        time += e[:dur] || 0.5
      end
      
      events
    end
    
    # Data corruption
    def self.corrupt(events, corruption: 0.3)
      events.map do |e|
        if rand < corruption
          e.merge(
            pitch: e[:pitch] + rand(-24..24),
            dur: e[:dur] * (0.1 + rand * 2),
            amp: rand * 0.5
          )
        else
          e
        end
      end
    end
    
    # Silence glitch (sudden dropouts)
    def self.dropout(events, probability: 0.15)
      events.reject { rand < probability }
    end
  end
end
