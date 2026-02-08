# lib/opn/structure.rb
# OPN Component 14: Structural Forms
# Inspired by: R Plus Seven's suite structure

module OPN
  module Structure
    # Collage form (abrupt section changes)
    class Collage
      def initialize
        @sections = []
      end
      
      def add_section(events, gap: 0.5)
        @sections << { events: events, gap: gap }
        self
      end
      
      def generate
        result = []
        time = 0
        
        @sections.each do |section|
          section[:events].each do |e|
            result << e.merge(at: e[:at] + time)
          end
          
          max_time = section[:events].map { |e| e[:at] + (e[:dur] || 0) }.max || 0
          time += max_time + section[:gap]
        end
        
        result
      end
    end
    
    # Through-composed (continuous development)
    def self.through_composed(seed_events, developments: 4, morph_rate: 0.2)
      events = seed_events.dup
      result = events.dup
      time = events.map { |e| e[:at] + (e[:dur] || 0) }.max
      
      developments.times do
        # Develop the material
        events = events.map do |e|
          if rand < morph_rate
            e.merge(
              pitch: e[:pitch] + [-2, -1, 1, 2, 5, 7].sample,
              dur: e[:dur] * (0.8 + rand * 0.4)
            )
          else
            e.dup
          end
        end
        
        events.each { |e| result << e.merge(at: e[:at] + time) }
        time += events.map { |e| e[:at] + (e[:dur] || 0) }.max
      end
      
      result
    end
    
    # Arc form (A-B-climax-B'-A')
    def self.arc_form(a_events:, b_events:, climax_events:)
      result = []
      time = 0
      
      # A
      a_events.each { |e| result << e.merge(at: e[:at] + time) }
      time += a_events.map { |e| e[:at] + (e[:dur] || 0) }.max + 1
      
      # B
      b_events.each { |e| result << e.merge(at: e[:at] + time) }
      time += b_events.map { |e| e[:at] + (e[:dur] || 0) }.max + 1
      
      # Climax
      climax_events.each { |e| result << e.merge(at: e[:at] + time) }
      time += climax_events.map { |e| e[:at] + (e[:dur] || 0) }.max + 1
      
      # B' (varied)
      b_events.map { |e| e.merge(pitch: e[:pitch] + 2) }.each { |e| result << e.merge(at: e[:at] + time) }
      time += b_events.map { |e| e[:at] + (e[:dur] || 0) }.max + 1
      
      # A' (quieter)
      a_events.map { |e| e.merge(amp: e[:amp] * 0.6) }.each { |e| result << e.merge(at: e[:at] + time) }
      
      result
    end
  end
end
