# lib/opn/transcendental.rb
# OPN Component 17: Transcendental Orchestrator
# The master conductor that combines all components

require_relative '../free_monad'

# Load all OPN components
Dir[File.join(__dir__, '*.rb')].each do |file|
  require file unless file.end_with?('transcendental.rb')
end

module OPN
  module Transcendental
    extend FreeMonad::DSL
    
    # Master generator combining all techniques
    class TranscendentalGenerator
      def initialize(seed: 42, duration: 120.0)
        @seed = seed
        @duration = duration
        srand(seed)
      end
      
      def generate
        events = []
        
        # Layer 1: Deep drone foundation
        events += Drone.evolving_drone(root: 36, duration: @duration, movement: 8)
        
        # Layer 2: Granular texture
        4.times do |i|
          start = i * @duration / 4
          cloud = Granular::GrainCloud.new(
            center_pitch: 60 + i * 7,
            density: 30,
            scatter: 8,
            duration: @duration / 4
          )
          events += cloud.generate.map { |e| e.merge(at: e[:at] + start) }
        end
        
        # Layer 3: Harmonic progression
        progression = [
          [48, :maj9], [53, :min11], [41, :sus4], [48, :cluster_wide],
          [55, :quartal], [50, :madd9], [45, :split_5ths], [48, :major]
        ]
        chord_dur = @duration / progression.length
        
        progression.each_with_index do |(root, type), i|
          Harmony.chord(root, type: type, duration: chord_dur * 0.9).each do |e|
            events << e.merge(at: e[:at] + i * chord_dur)
          end
        end
        
        # Layer 4: Arpeggiated figures
        arp_chords = [[48, 52, 55, 60], [53, 57, 60, 65], [55, 59, 62, 67]]
        arp_chords.each_with_index do |chord, i|
          start = i * @duration / 3
          arp_events = Arpeggios.filter_sweep_arp(chord, duration: @duration / 3)
          events += arp_events.map { |e| e.merge(at: e[:at] + start) }
        end
        
        # Layer 5: Glitch interruptions
        5.times do
          glitch_time = rand * @duration
          pitch = 60 + rand(-12..12)
          events += Glitch.buffer_stutter(pitch, repeats: rand(8..24))
            .map { |e| e.merge(at: e[:at] + glitch_time) }
        end
        
        # Layer 6: Dynamic shaping
        events = Dynamics.breathing(events, cycle: 16.0)
        
        # Layer 7: Spatial processing
        events = Spatial.shimmer(events, density: 5, spread: 2.0)
        
        events.sort_by { |e| e[:at] }
      end
      
      def to_pattern
        events = generate
        
        notes = events.map do |e|
          if e[:pitches]
            FreeMonad::Suspend.new(FreeMonad::PlayChord.new(
              e[:pitches].map(&:round), e[:dur] || 0.5, e[:amp] || 0.3
            ))
          else
            FreeMonad::Suspend.new(FreeMonad::PlayNote.new(
              e[:pitch].round, e[:dur] || 0.5, e[:amp] || 0.3
            ))
          end
        end
        
        FreeMonad::Suspend.new(FreeMonad::Sequence.new(notes))
      end
    end
    
    # Presets
    def self.garden_of_delete(duration: 90.0)
      events = []
      
      # Uncanny MIDI orchestra
      events += MidiOrchestra.uncanny_strings(root: 48, duration: duration / 2)
      
      # Vocoder choir
      events += Vocoder.synth_choir(root: 60, duration: duration / 4)
        .map { |e| e.merge(at: e[:at] + duration / 2) }
      
      # Glitched and processed
      events = Glitch.corrupt(events, corruption: 0.1)
      events = Spectral.spectral_blur(events, blur_amount: 2)
      
      events
    end
    
    def self.r_plus_seven(duration: 120.0)
      events = []
      
      # Granular textures
      events += Granular.spectral_smear(fundamental: 36, partials: 12, duration: duration)
      
      # MIDI orchestration
      ensemble = MidiOrchestra::HyperrealEnsemble.new(
        voices: [:violin, :viola, :cello, :flute, :horn]
      )
      events += ensemble.progression(
        [48, 53, 45, 50, 55, 48],
        [:maj9, :min11, :sus4, :cluster_tight, :quartal, :major],
        duration_each: duration / 6
      )
      
      # Collage structure
      events = Samples.paulstretch(events, stretch: 1.5, density: 15)
      
      events
    end
    
    def self.age_of(duration: 60.0)
      events = []
      
      # Vocal textures
      voice = Vocoder::VocoderVoice.new(carrier_pitch: 48)
      events += voice.speak([:a, :e, :i, :o, :u, :a, :i, :u] * 4, duration_each: duration / 32)
      
      # Polyrhythmic layers
      poly = Polyrhythm::PolyLayer.new([3, 4, 5, 7])
      events += poly.generate(duration: duration, pitches: [48, 55, 60, 67])
      
      # Eccojam section
      phrase = (0..7).map { |i| { at: i * 0.25, pitch: 60 + [0, 2, 4, 5, 7, 5, 4, 2][i], dur: 0.2, amp: 0.4 } }
      events += Eccojam::ChopLoop.new(
        phrase.map { |e| e[:pitch] },
        phrase.map { |e| e[:dur] },
        loop_count: 8
      ).generate.map { |e| e.merge(at: e[:at] + duration / 2) }
      
      # Process
      events = Dynamics.emergence(events, duration: duration / 4)
      events = Spatial.room(events, size: :cathedral)
      
      events
    end
    
    # Build full transcendental piece
    def self.transcendental_piece(seed: 42, duration: 180.0)
      gen = TranscendentalGenerator.new(seed: seed, duration: duration)
      gen.generate
    end
  end
end
