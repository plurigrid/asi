# lib/opn/granular.rb
# OPN Component 1: Granular Microsound
# Inspired by: R Plus Seven, Replica

module OPN
  module Granular
    extend FreeMonad::DSL if defined?(FreeMonad)
    
    # Grain cloud generator
    # - Thousands of tiny sound particles
    # - Density controlled by probability
    # - Pitch scatter around center
    class GrainCloud
      def initialize(center_pitch: 60, density: 100, scatter: 12, duration: 8.0)
        @center = center_pitch
        @density = density  # grains per second
        @scatter = scatter  # semitones
        @duration = duration
      end
      
      def generate
        events = []
        time = 0
        grain_interval = 1.0 / @density
        
        while time < @duration
          # Gaussian scatter around center
          pitch = @center + (rand_gaussian * @scatter / 3).round
          pitch = pitch.clamp(24, 96)
          
          # Micro duration (1-50ms)
          dur = 0.001 + rand * 0.049
          
          # Amplitude envelope follows density
          amp = 0.05 + rand * 0.15
          
          events << { at: time, pitch: pitch, dur: dur, amp: amp }
          
          # Irregular timing
          time += grain_interval * (0.5 + rand)
        end
        
        events
      end
      
      def to_pattern
        events = generate
        notes = events.map do |e|
          FreeMonad::Suspend.new(FreeMonad::PlayNote.new(e[:pitch], e[:dur], e[:amp]))
        end
        FreeMonad::Suspend.new(FreeMonad::Sequence.new(notes))
      end
      
      private
      
      def rand_gaussian
        u1 = rand
        u2 = rand
        Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math::PI * u2)
      end
    end
    
    # Freeze frame: sustained grain at single pitch
    def self.freeze_frame(pitch, duration: 4.0, density: 50)
      cloud = GrainCloud.new(center_pitch: pitch, density: density, scatter: 0.5, duration: duration)
      cloud.generate
    end
    
    # Spectral smear: grains across harmonic series
    def self.spectral_smear(fundamental: 36, partials: 8, duration: 6.0)
      events = []
      partials.times do |n|
        freq_ratio = n + 1
        pitch = fundamental + (12 * Math.log2(freq_ratio)).round
        
        cloud = GrainCloud.new(center_pitch: pitch, density: 30 / (n + 1), scatter: 2, duration: duration)
        cloud.generate.each { |e| events << e }
      end
      events.sort_by { |e| e[:at] }
    end
  end
end
