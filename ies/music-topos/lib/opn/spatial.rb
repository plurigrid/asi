# lib/opn/spatial.rb
# OPN Component 16: Spatial Effects
# Inspired by: Commissions II, MYRIAD

module OPN
  module Spatial
    # Delay network
    def self.delay_network(events, taps: 4, feedback: 0.6, max_delay: 2.0)
      result = events.dup
      
      taps.times do |tap|
        delay = max_delay * (tap + 1) / taps
        amp_decay = feedback ** (tap + 1)
        
        events.each do |e|
          result << {
            at: e[:at] + delay,
            pitch: e[:pitch] + (tap > 2 ? 12 : 0),  # Octave up on later taps
            dur: e[:dur] * 1.2,
            amp: e[:amp] * amp_decay
          }
        end
      end
      
      result.sort_by { |e| e[:at] }
    end
    
    # Ping pong delay (alternating stereo, simulated as pitch)
    def self.ping_pong(events, delay_time: 0.375, repeats: 6)
      result = events.dup
      
      repeats.times do |r|
        direction = r.even? ? 1 : -1
        delay = delay_time * (r + 1)
        
        events.each do |e|
          result << {
            at: e[:at] + delay,
            pitch: e[:pitch] + direction * 0.1,  # Slight pitch for L/R
            dur: e[:dur],
            amp: e[:amp] * (0.8 ** (r + 1))
          }
        end
      end
      
      result.sort_by { |e| e[:at] }
    end
    
    # Shimmer reverb (octave-shifted delays)
    def self.shimmer(events, density: 10, spread: 4.0)
      result = events.dup
      
      density.times do |d|
        delay = rand * spread
        octave_shift = [0, 12, 24, -12].sample
        
        events.each do |e|
          result << {
            at: e[:at] + delay,
            pitch: (e[:pitch] + octave_shift).clamp(24, 96),
            dur: e[:dur] * (1 + delay / 2),
            amp: e[:amp] * 0.15
          }
        end
      end
      
      result.sort_by { |e| e[:at] }
    end
    
    # Room simulation (early reflections)
    def self.room(events, size: :medium)
      delays = case size
        when :small then [0.01, 0.02, 0.03, 0.05]
        when :medium then [0.02, 0.05, 0.08, 0.12, 0.18]
        when :large then [0.05, 0.1, 0.2, 0.35, 0.5, 0.7]
        when :cathedral then [0.1, 0.3, 0.6, 1.0, 1.5, 2.2, 3.0]
        else [0.02, 0.05, 0.08, 0.12, 0.18]
      end
      
      result = events.dup
      
      delays.each_with_index do |delay, i|
        amp_factor = 0.6 ** (i + 1)
        
        events.each do |e|
          result << {
            at: e[:at] + delay,
            pitch: e[:pitch],
            dur: e[:dur] * (1 + delay * 0.5),
            amp: e[:amp] * amp_factor
          }
        end
      end
      
      result.sort_by { |e| e[:at] }
    end
  end
end
