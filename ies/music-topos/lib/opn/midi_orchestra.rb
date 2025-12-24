# lib/opn/midi_orchestra.rb
# OPN Component 3: Hyperreal MIDI Orchestra
# Inspired by: Garden of Delete, Age Of

module OPN
  module MidiOrchestra
    # Fake orchestra: MIDI strings, brass, woodwinds layered
    class HyperrealEnsemble
      RANGES = {
        violin: [55, 96],
        viola: [48, 84],
        cello: [36, 72],
        bass: [28, 55],
        flute: [60, 96],
        oboe: [58, 91],
        clarinet: [50, 89],
        bassoon: [34, 72],
        horn: [41, 77],
        trumpet: [55, 82],
        trombone: [40, 72],
        tuba: [29, 55]
      }
      
      def initialize(voices: [:violin, :cello, :horn])
        @voices = voices
      end
      
      def chord(root, quality: :major, duration: 2.0, amp: 0.4)
        intervals = case quality
          when :major then [0, 4, 7]
          when :minor then [0, 3, 7]
          when :dim then [0, 3, 6]
          when :aug then [0, 4, 8]
          when :maj7 then [0, 4, 7, 11]
          when :min7 then [0, 3, 7, 10]
          else [0, 4, 7]
        end
        
        events = []
        
        @voices.each_with_index do |voice, i|
          range = RANGES[voice] || [36, 84]
          interval = intervals[i % intervals.length]
          pitch = root + interval
          
          # Find octave within range
          while pitch < range[0]
            pitch += 12
          end
          while pitch > range[1]
            pitch -= 12
          end
          
          # Slight timing humanization
          time_offset = (rand - 0.5) * 0.02
          
          events << {
            at: [time_offset, 0].max,
            pitch: pitch,
            dur: duration * (0.9 + rand * 0.2),
            amp: amp * (0.8 + rand * 0.4),
            voice: voice
          }
        end
        
        events
      end
      
      def progression(roots, qualities, duration_each: 2.0)
        events = []
        time = 0
        
        roots.zip(qualities).each do |root, quality|
          chord(root, quality: quality, duration: duration_each).each do |e|
            events << e.merge(at: e[:at] + time)
          end
          time += duration_each
        end
        
        events
      end
    end
    
    # Uncanny valley strings
    def self.uncanny_strings(root: 48, duration: 8.0)
      ensemble = HyperrealEnsemble.new(voices: [:violin, :violin, :viola, :cello, :bass])
      
      # Cluster voicing (OPN trademark)
      events = []
      cluster = [root, root + 1, root + 4, root + 5, root + 7]
      
      cluster.each_with_index do |pitch, i|
        # Staggered entries
        events << {
          at: i * 0.3,
          pitch: pitch,
          dur: duration - i * 0.3,
          amp: 0.25 - i * 0.03
        }
      end
      
      events
    end
  end
end
