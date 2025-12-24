# lib/opn/drone.rb
# OPN Component 6: Drone / Cathedral Space
# Inspired by: Rifts, Betrayed in the Octagon

module OPN
  module Drone
    # Infinite drone generator
    class InfiniteDrone
      def initialize(root: 36, harmonics: 8)
        @root = root
        @harmonics = harmonics
      end
      
      def generate(duration: 32.0)
        events = []
        
        # Fundamental
        events << {
          at: 0,
          pitch: @root,
          dur: duration,
          amp: 0.4
        }
        
        # Harmonic series with beating
        @harmonics.times do |n|
          ratio = n + 2  # 2nd harmonic onwards
          pitch = @root + (12 * Math.log2(ratio)).round
          
          # Slight detune for beating
          detune = (rand - 0.5) * 0.2
          
          events << {
            at: rand * 0.5,  # Staggered entry
            pitch: pitch + detune,
            dur: duration - rand,
            amp: 0.3 / ratio
          }
        end
        
        events
      end
    end
    
    # Evolving drone with movement
    def self.evolving_drone(root: 36, duration: 64.0, movement: 5)
      events = []
      segment_dur = duration / movement
      
      current_pitch = root
      movement.times do |i|
        drone = InfiniteDrone.new(root: current_pitch, harmonics: 6)
        drone.generate(duration: segment_dur).each do |e|
          events << e.merge(at: e[:at] + i * segment_dur)
        end
        
        # Move root
        current_pitch += [-5, -3, 0, 2, 4, 7].sample
        current_pitch = current_pitch.clamp(24, 48)
      end
      
      events
    end
    
    # Cathedral reverb simulation (layered delays)
    def self.cathedral_wash(pitches, feedback: 5, delay: 0.5)
      events = []
      
      pitches.each_with_index do |pitch, i|
        base_time = i * 0.5
        amp = 0.4
        
        (feedback + 1).times do |d|
          events << {
            at: base_time + d * delay,
            pitch: pitch,
            dur: delay * 1.5,
            amp: amp
          }
          amp *= 0.7
        end
      end
      
      events
    end
  end
end
