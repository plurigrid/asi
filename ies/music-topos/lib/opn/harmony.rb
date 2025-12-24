# lib/opn/harmony.rb
# OPN Component 13: Harmonic Language
# Inspired by: Age Of, Garden of Delete

module OPN
  module Harmony
    # OPN-style chord vocabulary
    CHORD_TYPES = {
      # Standard
      major: [0, 4, 7],
      minor: [0, 3, 7],
      
      # Extended
      maj9: [0, 4, 7, 11, 14],
      min11: [0, 3, 7, 10, 14, 17],
      
      # Suspended
      sus2: [0, 2, 7],
      sus4: [0, 5, 7],
      
      # Cluster (OPN favorite)
      cluster_tight: [0, 1, 2, 3],
      cluster_wide: [0, 2, 5, 7],
      
      # Add chords
      add9: [0, 4, 7, 14],
      madd9: [0, 3, 7, 14],
      
      # Split
      split_5ths: [0, 7, 14, 21],
      
      # Quartal
      quartal: [0, 5, 10, 15],
      quintal: [0, 7, 14, 21]
    }
    
    def self.chord(root, type: :major, inversion: 0, duration: 2.0, amp: 0.4)
      intervals = CHORD_TYPES[type] || CHORD_TYPES[:major]
      
      pitches = intervals.map { |i| root + i }
      
      # Apply inversion
      inversion.times do
        pitches[0] += 12
        pitches = pitches.rotate(1)
      end
      
      pitches.map.with_index do |p, i|
        {
          at: i * 0.02,  # Slight strum
          pitch: p.clamp(24, 96),
          dur: duration,
          amp: amp / (i * 0.1 + 1)
        }
      end
    end
    
    # Voice leading between two chords
    def self.voice_lead(chord1, chord2, duration: 4.0)
      events = []
      steps = 8
      
      chord1.zip(chord2).each_with_index do |(p1, p2), voice|
        p1 ||= chord1.last
        p2 ||= chord2.first
        
        steps.times do |s|
          progress = s.to_f / (steps - 1)
          pitch = p1 + (p2 - p1) * progress
          
          events << {
            at: s * (duration / steps),
            pitch: pitch.round,
            dur: duration / steps * 1.2,
            amp: 0.25,
            voice: voice
          }
        end
      end
      
      events
    end
    
    # Modal interchange
    def self.modal_interchange(root: 60, modes: [:major, :minor, :sus4, :cluster_tight])
      events = []
      time = 0
      
      modes.each do |mode|
        events += chord(root, type: mode, duration: 2.0).map { |e| e.merge(at: e[:at] + time) }
        time += 2.5
      end
      
      events
    end
  end
end
