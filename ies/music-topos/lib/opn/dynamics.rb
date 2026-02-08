# lib/opn/dynamics.rb
# OPN Component 8: Extreme Dynamic Range
# Inspired by: Garden of Delete, Age Of's dynamic contrasts

module OPN
  module Dynamics
    # Sudden silence
    def self.hard_cut(events, at_time:)
      events.select { |e| e[:at] < at_time }
    end
    
    # Crescendo from nothing
    def self.emergence(events, duration:)
      events.map do |e|
        progress = [e[:at] / duration, 1.0].min
        e.merge(amp: e[:amp] * progress * progress)
      end
    end
    
    # Sudden loudness spike
    def self.impact(pitch, duration: 0.5, amp: 0.9)
      [
        { at: 0, pitch: pitch, dur: duration, amp: amp },
        { at: 0, pitch: pitch - 12, dur: duration * 1.2, amp: amp * 0.8 },
        { at: 0, pitch: pitch + 12, dur: duration * 0.8, amp: amp * 0.6 }
      ]
    end
    
    # Breathing dynamics
    def self.breathing(events, cycle: 4.0)
      events.map do |e|
        phase = (e[:at] % cycle) / cycle
        breath = 0.3 + 0.7 * Math.sin(phase * Math::PI)
        e.merge(amp: e[:amp] * breath)
      end
    end
    
    # Swell
    def self.swell(pitch, duration: 8.0, peak_at: 0.7)
      events = []
      steps = (duration / 0.1).to_i
      
      steps.times do |i|
        progress = i.to_f / steps
        amp = if progress < peak_at
          progress / peak_at * 0.8
        else
          0.8 * (1 - (progress - peak_at) / (1 - peak_at))
        end
        
        events << {
          at: i * 0.1,
          pitch: pitch,
          dur: 0.15,
          amp: amp
        }
      end
      
      events
    end
    
    # Subito piano (sudden quiet)
    def self.subito_piano(events, at_time:, reduction: 0.2)
      events.map do |e|
        if e[:at] >= at_time
          e.merge(amp: e[:amp] * reduction)
        else
          e
        end
      end
    end
  end
end
