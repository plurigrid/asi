# lib/quantum_industrial_patterns.rb
#
# QUANTUM INDUSTRIAL PATTERNS
# Synthesizing: Bob Coecke's Quantum Guitar, CJ Carr's Neural Synthesis,
# and the aesthetics of Daniel Avery, Loraine James, Machine Girl
#
# Core concepts:
# - Quantum superposition → simultaneous contradictory states
# - Perturbative evolution → patterns that mutate via interaction
# - Nonstandard scales → microtonal, spectral, stochastic tunings
# - Neural synthesis artifacts → glitch as feature, not bug

require_relative 'free_monad'

module QuantumIndustrialPatterns
  extend FreeMonad::DSL
  
  # ============================================================================
  # NONSTANDARD SCALES
  # Beyond 12-TET: microtonal, spectral, stochastic
  # ============================================================================
  
  module Scales
    # Bohlen-Pierce scale (13 steps in 3:1 ratio instead of 12 in 2:1)
    BOHLEN_PIERCE = [0, 1.46, 2.34, 3.80, 4.68, 6.14, 7.02, 7.90, 9.36, 10.24, 11.70, 12.58, 13.46]
    
    # Wendy Carlos Alpha scale (78 cents per step)
    ALPHA_SCALE = (0..15).map { |i| i * 0.78 }
    
    # Spectral scale based on overtone series (just intonation ratios)
    SPECTRAL_RATIOS = [1, 17/16.0, 9/8.0, 19/16.0, 5/4.0, 21/16.0, 11/8.0, 
                       3/2.0, 13/8.0, 27/16.0, 7/4.0, 15/8.0, 2]
    
    # Gamelan-inspired pelog (unequal temperament)
    PELOG = [0, 1.2, 2.8, 5.0, 7.1, 8.3, 10.5, 12]
    
    # Xenakis sieve (stochastic pitch selection)
    def self.xenakis_sieve(modulus, residues, range: 36..96)
      range.select { |n| residues.include?(n % modulus) }
    end
    
    # Quantum superposition scale - multiple scales simultaneously
    def self.quantum_scale(scales, weights: nil)
      weights ||= Array.new(scales.length, 1.0 / scales.length)
      ->(base_pitch) {
        # Return weighted random selection from all scales
        scale = scales.sample # Simplified; real impl would use weights
        degree = rand(scale.length)
        base_pitch + scale[degree]
      }
    end
    
    # Machine Girl / breakcore - rapid pitch modulation
    def self.glitch_pitch(base, intensity: 0.5)
      deviation = (rand - 0.5) * 2 * intensity * 12  # Up to ±6 semitones
      base + deviation
    end
    
    # Loraine James - subtle detuning for warmth
    def self.humanize_pitch(pitch, cents: 10)
      pitch + (rand - 0.5) * 2 * (cents / 100.0)
    end
    
    # Daniel Avery - hypnotic drone with beating
    def self.beating_pair(base, beat_freq: 1.5)
      cents_offset = 1200 * Math.log2((440 + beat_freq) / 440.0)
      [base, base + cents_offset / 100.0]
    end
  end
  
  # ============================================================================
  # PERTURBATIVE EVOLUTION
  # Patterns that mutate through interaction
  # ============================================================================
  
  module Perturbation
    # Apply quantum-style measurement collapse
    def self.measure(superposition)
      superposition.sample  # Collapse to single state
    end
    
    # Continuous rotation (like quantum gate)
    def self.rotate(value, angle, range:)
      min, max = range.minmax
      normalized = (value - min).to_f / (max - min)
      rotated = (normalized + angle) % 1.0
      min + rotated * (max - min)
    end
    
    # Perturbative probe - small random walk
    def self.probe(pattern, epsilon: 0.1)
      case pattern
      when Numeric
        pattern + (rand - 0.5) * 2 * epsilon * pattern.abs
      when Array
        pattern.map { |p| probe(p, epsilon: epsilon) }
      else
        pattern
      end
    end
    
    # Evolution via feedback (CJ Carr style - artifacts become features)
    def self.feedback_evolve(history, decay: 0.8, mutation_rate: 0.1)
      return nil if history.empty?
      
      recent = history.last(5)
      # Weighted average with decay
      weighted = recent.each_with_index.map { |v, i| v * (decay ** (recent.length - i - 1)) }
      base = weighted.sum / weighted.length
      
      # Mutation
      if rand < mutation_rate
        base + (rand - 0.5) * 12  # Jump by up to ±6 semitones
      else
        base
      end
    end
    
    # Quantum entanglement - two patterns that affect each other
    def self.entangle(pattern_a, pattern_b, coupling: 0.5)
      # When one is measured, the other is affected
      measured_a = measure(pattern_a)
      affected_b = pattern_b.map { |p| p + (measured_a - p) * coupling }
      [measured_a, affected_b]
    end
  end
  
  # ============================================================================
  # ARTIST-INSPIRED PATTERNS
  # ============================================================================
  
  class VirtuosoPatternBuilder
    extend FreeMonad::DSL
    
    # Daniel Avery style: hypnotic, textured techno
    # Key elements: drone, subtle modulation, psychedelic synth washes
    def self.daniel_avery_texture(base_pitch: 36, duration: 16.0)
      # Low drone with beating frequencies
      beating = Scales.beating_pair(base_pitch, beat_freq: 0.7)
      
      sequence!(
        # Foundation drone
        parallel!(
          play_note!(beating[0], duration, 0.35),
          play_note!(beating[1], duration, 0.30),
          play_note!(base_pitch + 12, duration, 0.15)  # Octave reinforcement
        ),
        # Overlapping texture sweeps
        parallel!(
          sequence!(
            *8.times.map do |i|
              sequence!(
                rest!(i * 2.0),
                play_note!(base_pitch + 19 + (i % 3), 4.0, 0.08 + i * 0.01)
              )
            end
          )
        )
      )
    end
    
    # Loraine James style: glitchy IDM with emotional depth
    # Key elements: stuttering rhythms, jazz harmony, vulnerable vocals (represented by high melodic lines)
    def self.loraine_james_fragment(root: 48)
      # Jazz-influenced chord voicings with IDM fragmentation
      voicings = [
        [root, root + 4, root + 7, root + 11],      # maj7
        [root + 2, root + 5, root + 9, root + 12],  # minor add9
        [root - 2, root + 3, root + 7, root + 10],  # dim7
      ]
      
      events = []
      current_beat = 0
      
      voicings.each_with_index do |chord, i|
        # Glitchy stuttering
        stutters = rand(3..6)
        stutters.times do |s|
          duration = rand(0.05..0.2)
          # Humanized pitches
          humanized = chord.map { |p| Scales.humanize_pitch(p, cents: 15) }
          events << play_chord!(humanized.map(&:round), duration, 0.2 - s * 0.02)
          events << rest!(rand(0.02..0.08))
        end
        
        # Let the chord breathe
        events << play_chord!(chord, 0.8, 0.25)
        events << rest!(0.3)
      end
      
      sequence!(*events)
    end
    
    # Machine Girl style: aggressive breakcore with digital hardcore
    # Key elements: mangled amen breaks, distortion, extreme tempo
    def self.machine_girl_assault(base_pitch: 36)
      events = []
      
      # Rapid-fire hits with pitch chaos
      32.times do |i|
        pitch = base_pitch + rand(-12..24)
        pitch = Scales.glitch_pitch(pitch, intensity: 0.8)
        
        duration = [0.03, 0.05, 0.08, 0.1].sample
        amp = rand(0.2..0.6)
        
        events << play_note!(pitch.round, duration, amp)
        
        # Irregular rests (breakcore syncopation)
        rest_time = [0.02, 0.03, 0.05, 0.08, 0.12].sample
        events << rest!(rest_time) if rand > 0.3
      end
      
      # Massive bass drop
      events << play_chord!([24, 36], 0.3, 0.7)
      events << rest!(0.15)
      events << play_chord!([24, 36], 0.3, 0.7)
      
      sequence!(*events)
    end
    
    # Mica Levi style: unsettling, cinematic, alien
    # Key elements: microtonal clusters, extreme register contrast, dread
    def self.mica_levi_dread(base: 30)
      sequence!(
        # Very low cluster
        play_chord!([base, base + 1, base + 2], 3.0, 0.4),
        rest!(0.5),
        
        # Piercing high contrast
        play_note!(96, 1.5, 0.12),
        play_note!(97, 1.2, 0.10),
        rest!(0.8),
        
        # Sliding microtonal figure (represented by semitone clusters)
        *5.times.flat_map do |i|
          [
            play_chord!([60 + i, 61 + i, 63 + i], 0.3, 0.15 - i * 0.02),
            rest!(0.1)
          ]
        end,
        
        # Return to dread
        play_chord!([base - 12, base, base + 1], 4.0, 0.5)
      )
    end
    
    # Quantum Guitar style (Bob Coecke): superposition states, measurement collapse
    def self.quantum_guitar_superposition(base: 48)
      # Create superposition of multiple pitch states
      states = [
        [base, base + 4, base + 7],       # Major
        [base, base + 3, base + 7],       # Minor
        [base, base + 6, base + 10],      # Diminished
        [base, base + 4, base + 8]        # Augmented
      ]
      
      events = []
      
      # Quantum uncertainty - play multiple states with decreasing certainty
      states.each_with_index do |chord, i|
        certainty = 0.4 - i * 0.08
        events << play_chord!(chord, 0.5, certainty)
        events << rest!(0.1)
      end
      
      # Measurement collapse - commit to one state
      collapsed = states.sample
      events << rest!(0.3)
      events << play_chord!(collapsed, 2.0, 0.5)
      
      # Classical-quantum transition
      events << rest!(0.2)
      10.times do |i|
        # Gradually add uncertainty
        pitch_spread = i * 0.5
        chord = collapsed.map { |p| (p + (rand - 0.5) * pitch_spread).round }
        events << play_chord!(chord, 0.2, 0.3 - i * 0.02)
        events << rest!(0.05)
      end
      
      sequence!(*events)
    end
    
    # CJ Carr / Dadabots style: neural synthesis artifacts as features
    def self.neural_artifact_texture(duration: 8.0)
      events = []
      time = 0
      
      srand(42)  # Deterministic "neural" randomness
      
      while time < duration
        # Simulate neural network temperature/stochasticity
        temperature = 0.5 + Math.sin(time * 0.5) * 0.3
        
        # Pitch from "latent space" - clustered around certain attractors
        attractors = [36, 48, 60, 72, 84]
        base = attractors.sample
        pitch = (base + (rand - 0.5) * 24 * temperature).round
        pitch = pitch.clamp(24, 96)
        
        # Duration varies with temperature
        dur = (0.05 + rand * 0.3 * temperature)
        amp = 0.1 + rand * 0.25
        
        events << play_note!(pitch, dur, amp)
        
        # "Hallucinated" rests
        rest_time = rand * 0.15 * temperature
        events << rest!(rest_time) if rest_time > 0.02
        
        time += dur + rest_time
      end
      
      sequence!(*events)
    end
  end
  
  # ============================================================================
  # INTERMIXING / MORPHING
  # Delight through unexpected combinations
  # ============================================================================
  
  class Intermixer
    extend FreeMonad::DSL
    
    # Crossfade between two pattern styles
    def self.morph(pattern_a, pattern_b, steps: 8)
      sequence!(
        *steps.times.map do |i|
          blend = i.to_f / (steps - 1)
          if blend < 0.5
            pattern_a
          else
            pattern_b
          end
        end
      )
    end
    
    # Interleave patterns at phrase level
    def self.interleave(*patterns)
      sequence!(*patterns)
    end
    
    # Collision: run patterns in parallel with interference
    def self.collide(pattern_a, pattern_b)
      parallel!(pattern_a, pattern_b)
    end
    
    # The Virtuoso Showcase: cycle through all artist styles
    def self.virtuoso_showcase
      sequence!(
        section_marker("=== DANIEL AVERY: HYPNOTIC DRONE ==="),
        VirtuosoPatternBuilder.daniel_avery_texture(base_pitch: 36, duration: 8.0),
        rest!(0.5),
        
        section_marker("=== LORAINE JAMES: GLITCH IDM ==="),
        VirtuosoPatternBuilder.loraine_james_fragment(root: 48),
        rest!(0.5),
        
        section_marker("=== MACHINE GIRL: BREAKCORE ASSAULT ==="),
        VirtuosoPatternBuilder.machine_girl_assault(base_pitch: 36),
        rest!(0.5),
        
        section_marker("=== MICA LEVI: CINEMATIC DREAD ==="),
        VirtuosoPatternBuilder.mica_levi_dread(base: 30),
        rest!(0.5),
        
        section_marker("=== QUANTUM GUITAR: SUPERPOSITION ==="),
        VirtuosoPatternBuilder.quantum_guitar_superposition(base: 48),
        rest!(0.5),
        
        section_marker("=== CJ CARR: NEURAL ARTIFACTS ==="),
        VirtuosoPatternBuilder.neural_artifact_texture(duration: 6.0),
        rest!(0.5),
        
        section_marker("=== FINALE: COLLISION ==="),
        collide(
          VirtuosoPatternBuilder.machine_girl_assault(base_pitch: 30),
          VirtuosoPatternBuilder.mica_levi_dread(base: 36)
        )
      )
    end
    
    private
    
    def self.section_marker(name)
      FreeMonad::Pure.new(name)
    end
  end
end
