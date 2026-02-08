# lib/opn/repetition.rb
# OPN Component 12: Emotional Repetition
# Inspired by: Still Life, Nobody Here

module OPN
  module Repetition
    # Obsessive loop
    def self.obsessive_loop(phrase, repetitions: 16, subtle_variation: true)
      events = []
      phrase_duration = phrase.map { |e| e[:at] + (e[:dur] || 0.5) }.max
      
      repetitions.times do |rep|
        phrase.each do |e|
          variation = if subtle_variation
            {
              pitch: e[:pitch] + (rand > 0.9 ? [-1, 1].sample : 0),
              amp: e[:amp] * (0.95 + rand * 0.1),
              dur: e[:dur] * (0.98 + rand * 0.04)
            }
          else
            {}
          end
          
          events << e.merge(variation).merge(at: e[:at] + rep * phrase_duration)
        end
      end
      
      events
    end
    
    # Decaying loop (memory fading)
    def self.memory_fade(phrase, loops: 8)
      events = []
      phrase_duration = phrase.map { |e| e[:at] + (e[:dur] || 0.5) }.max
      
      loops.times do |l|
        decay = 1.0 - (l.to_f / loops) * 0.7
        
        phrase.each do |e|
          # Some notes disappear over time
          next if rand > decay + 0.3
          
          events << e.merge(
            at: e[:at] + l * phrase_duration,
            amp: e[:amp] * decay,
            pitch: e[:pitch] - (l * 0.1).round  # Tape slowdown
          )
        end
      end
      
      events
    end
    
    # Hypnotic ostinato
    def self.ostinato(notes, duration: 32.0, note_duration: 0.25)
      events = []
      time = 0
      i = 0
      
      while time < duration
        events << {
          at: time,
          pitch: notes[i % notes.length],
          dur: note_duration * 0.9,
          amp: 0.35 + Math.sin(time * 0.5) * 0.1
        }
        
        time += note_duration
        i += 1
      end
      
      events
    end
    
    # Micro-repetition (stutter on single note)
    def self.micro_stutter(pitch, times: 32, total_duration: 2.0)
      dur = total_duration / times
      
      times.times.map do |i|
        {
          at: i * dur,
          pitch: pitch,
          dur: dur * 0.7,
          amp: 0.4 - i * 0.01
        }
      end
    end
  end
end
