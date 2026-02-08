# lib/opn/polyrhythm.rb
# OPN Component 9: Polyrhythmic Layers
# Inspired by: Love in the Time of Lexapro, Age Of

module OPN
  module Polyrhythm
    # Multiple simultaneous time signatures
    class PolyLayer
      def initialize(divisions)
        @divisions = divisions  # e.g., [3, 4, 5, 7]
      end
      
      def generate(duration: 16.0, pitches: nil)
        events = []
        
        @divisions.each_with_index do |div, layer|
          pitch = pitches ? pitches[layer % pitches.length] : 48 + layer * 7
          interval = duration / (div * 4)  # 4 cycles
          
          time = 0
          while time < duration
            events << {
              at: time,
              pitch: pitch,
              dur: interval * 0.5,
              amp: 0.25 - layer * 0.03,
              layer: layer
            }
            time += interval
          end
        end
        
        events.sort_by { |e| e[:at] }
      end
    end
    
    # Phase shifting (Reich-inspired)
    def self.phase_shift(pattern, copies: 2, drift: 0.01)
      events = []
      
      copies.times do |c|
        offset = 0
        pattern.each do |e|
          events << e.merge(
            at: e[:at] + offset,
            amp: e[:amp] / copies
          )
          offset += drift  # Gradually drifts out of phase
        end
      end
      
      events.sort_by { |e| e[:at] }
    end
    
    # Metric modulation
    def self.metric_modulation(events, old_div:, new_div:, at_time:)
      ratio = old_div.to_f / new_div
      
      events.map do |e|
        if e[:at] >= at_time
          new_time = at_time + (e[:at] - at_time) * ratio
          e.merge(at: new_time, dur: e[:dur] * ratio)
        else
          e
        end
      end
    end
    
    # Additive rhythm (Gamelan-inspired)
    def self.additive(cycle_lengths, duration: 16.0)
      events = []
      
      cycle_lengths.each_with_index do |cycle, i|
        pitch = 60 + i * 5
        time = 0
        beat_dur = cycle.to_f / cycle_lengths.sum
        
        while time < duration
          events << {
            at: time,
            pitch: pitch,
            dur: beat_dur * 0.5,
            amp: 0.3
          }
          time += beat_dur * cycle
        end
      end
      
      events.sort_by { |e| e[:at] }
    end
  end
end
