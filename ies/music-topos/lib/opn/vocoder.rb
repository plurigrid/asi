# lib/opn/vocoder.rb
# OPN Component 4: Vocoder / Voice Synthesis
# Inspired by: Mutant Standard, Age Of's vocal processing

module OPN
  module Vocoder
    # Simulate vocoded voice as chord clusters
    class VocoderVoice
      FORMANTS = {
        a: [730, 1090, 2440],
        e: [530, 1840, 2480],
        i: [270, 2290, 3010],
        o: [570, 840, 2410],
        u: [440, 1020, 2240]
      }
      
      def initialize(carrier_pitch: 48)
        @carrier = carrier_pitch
      end
      
      def vowel(v, duration: 1.0, amp: 0.3)
        formants = FORMANTS[v] || FORMANTS[:a]
        
        events = []
        
        # Carrier + formant-derived pitches
        formants.each_with_index do |freq, i|
          # Approximate formant as pitch offset
          pitch = @carrier + (12 * Math.log2(freq / 261.63)).round
          pitch = pitch.clamp(24, 96)
          
          events << {
            at: 0,
            pitch: pitch,
            dur: duration,
            amp: amp / (i + 1)  # Higher formants quieter
          }
        end
        
        events
      end
      
      def speak(vowels, duration_each: 0.5)
        events = []
        time = 0
        
        vowels.each do |v|
          vowel(v, duration: duration_each).each do |e|
            events << e.merge(at: e[:at] + time)
          end
          time += duration_each
        end
        
        events
      end
    end
    
    # Robot voice effect
    def self.robot_voice(pitches, duration_each: 0.3)
      events = []
      time = 0
      
      pitches.each do |pitch|
        # Quantized, mechanical timing
        # Multiple detuned copies for chorus
        [-0.1, 0, 0.1].each do |detune|
          events << {
            at: time,
            pitch: pitch + detune,
            dur: duration_each * 0.9,
            amp: 0.2
          }
        end
        time += duration_each
      end
      
      events
    end
    
    # Choir pad
    def self.synth_choir(root: 48, duration: 4.0)
      voice = VocoderVoice.new(carrier_pitch: root)
      
      # Cycle through vowels slowly
      events = []
      [:a, :e, :i, :o, :u].each_with_index do |v, i|
        voice.vowel(v, duration: duration / 5).each do |e|
          events << e.merge(at: e[:at] + i * duration / 5)
        end
      end
      
      events
    end
  end
end
