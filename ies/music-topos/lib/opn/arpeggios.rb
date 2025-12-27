# lib/opn/arpeggios.rb
# OPN Component 5: Retro-Futurist Arpeggios
# Inspired by: Returnal, Zone's, R Plus Seven

module OPN
  module Arpeggios
    # Classic synth arpeggiator patterns
    PATTERNS = {
      up: ->(notes) { notes },
      down: ->(notes) { notes.reverse },
      updown: ->(notes) { notes + notes[1..-2].reverse },
      random: ->(notes) { notes.shuffle },
      played: ->(notes) { notes },  # As played order
      converge: ->(notes) {
        result = []
        (notes.length / 2.0).ceil.times do |i|
          result << notes[i]
          result << notes[-(i+1)] if i != notes.length - i - 1
        end
        result
      }
    }
    
    class Arpeggiator
      def initialize(chord, pattern: :up, octaves: 2, rate: 0.125)
        @chord = chord.sort
        @pattern = pattern
        @octaves = octaves
        @rate = rate  # beats per note
      end
      
      def generate(bars: 4)
        # Build full note set across octaves
        notes = []
        @octaves.times do |oct|
          @chord.each do |pitch|
            notes << pitch + oct * 12
          end
        end
        
        # Apply pattern
        ordered = PATTERNS[@pattern].call(notes)
        
        events = []
        time = 0
        beats = bars * 4  # Assuming 4/4
        
        while time < beats
          ordered.each do |pitch|
            break if time >= beats
            
            events << {
              at: time,
              pitch: pitch,
              dur: @rate * 0.8,
              amp: 0.3 + (pitch - @chord.first) * 0.005
            }
            
            time += @rate
          end
        end
        
        events
      end
    end
    
    # OPN-style arp with filter sweep simulation
    def self.filter_sweep_arp(chord, duration: 8.0)
      arp = Arpeggiator.new(chord, pattern: :updown, octaves: 3, rate: 0.0625)
      events = arp.generate(bars: (duration / 4).ceil)
      
      # Simulate filter sweep with amplitude envelope
      events.each_with_index do |e, i|
        progress = e[:at] / duration
        # Sweep up then down
        filter_sim = Math.sin(progress * Math::PI)
        e[:amp] *= 0.5 + filter_sim * 0.5
      end
      
      events
    end
    
    # Broken arp (missing notes, irregular)
    def self.broken_arp(chord, density: 0.7, duration: 8.0)
      arp = Arpeggiator.new(chord, pattern: :random, octaves: 2, rate: 0.125)
      events = arp.generate(bars: (duration / 4).ceil)
      
      # Remove some notes
      events.select { rand < density }
    end
  end
end
