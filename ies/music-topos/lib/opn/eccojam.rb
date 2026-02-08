# lib/opn/eccojam.rb
# OPN Component 2: Eccojam / Plunderphonics
# Inspired by: Chuck Person's Eccojams, Replica

module OPN
  module Eccojam
    # Chop and loop a melodic fragment
    class ChopLoop
      def initialize(pitches, durations, loop_count: 4, decay: 0.95)
        @pitches = pitches
        @durations = durations
        @loop_count = loop_count
        @decay = decay
      end
      
      def generate
        events = []
        time = 0
        amp = 0.6
        
        @loop_count.times do |loop_idx|
          @pitches.zip(@durations).each do |pitch, dur|
            # Pitch drift down over loops (tape degradation)
            drifted_pitch = pitch - (loop_idx * 0.1).round
            
            # Duration stretch
            stretched_dur = dur * (1 + loop_idx * 0.05)
            
            events << {
              at: time,
              pitch: drifted_pitch,
              dur: stretched_dur,
              amp: amp
            }
            
            time += stretched_dur
          end
          
          amp *= @decay
        end
        
        events
      end
    end
    
    # Slowed and reverbed sample simulation
    def self.slowed_sample(pitches, original_tempo: 120, slowdown: 0.5)
      durations = pitches.map { 60.0 / original_tempo / slowdown }
      
      events = []
      time = 0
      
      pitches.each_with_index do |pitch, i|
        # Transpose down by slowdown factor (pitch drops with speed)
        transposed = pitch - (12 * Math.log2(1.0 / slowdown)).round
        
        events << {
          at: time,
          pitch: transposed.clamp(24, 96),
          dur: durations[i] * 1.5,  # Overlap for reverb effect
          amp: 0.4
        }
        
        time += durations[i]
      end
      
      events
    end
    
    # Stutter edit
    def self.stutter(pitch, total_duration: 2.0, stutter_count: 8)
      events = []
      stutter_dur = total_duration / stutter_count
      
      stutter_count.times do |i|
        # Amplitude decay
        amp = 0.5 * (1 - i.to_f / stutter_count * 0.7)
        
        events << {
          at: i * stutter_dur,
          pitch: pitch,
          dur: stutter_dur * 0.8,
          amp: amp
        }
      end
      
      events
    end
  end
end
