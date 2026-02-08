# lib/maximum_dynamism.rb
#
# MAXIMUM DYNAMISM: Universal Derangement System
#
# Every component of every configuration of every in-stream action space
# degree of freedom is derangeable with randomness.
#
# ============================================================================
# THEORETICAL FOUNDATIONS
# ============================================================================
#
# DEGREES OF FREEDOM in musical space:
#   1. PITCH: fundamental frequency, harmonics, microtuning
#   2. TIME: onset, duration, tempo, phase
#   3. AMPLITUDE: loudness, envelope, dynamics
#   4. TIMBRE: spectral content, formants, noise
#   5. SPACE: pan, reverb, distance (when applicable)
#   6. STRUCTURE: sequence order, repetition, branching
#   7. META: the derangement parameters themselves
#
# DERANGEMENT STRATEGIES:
#   - Gaussian: Normal distribution around original value
#   - Uniform: Equal probability within range
#   - Lévy flight: Heavy-tailed jumps (rare large deviations)
#   - Brownian: Cumulative random walk
#   - Chaotic: Deterministic chaos (logistic map, etc.)
#   - Quantum: Superposition collapse
#   - Permutation: Reordering without value change
#
# The MODULE ACTION with derangement:
#   Pattern ⊗ Matter ⊗ Entropy → Deranged Events
#
# ============================================================================

require_relative 'free_monad'
require_relative 'quantum_aphex_autechre'

module MaximumDynamism
  
  # ============================================================================
  # ENTROPY SOURCES
  # Different flavors of randomness
  # ============================================================================
  
  module EntropySources
    # Standard Gaussian (bell curve)
    def self.gaussian(mean: 0, stddev: 1)
      # Box-Muller transform
      u1 = rand
      u2 = rand
      z = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math::PI * u2)
      mean + z * stddev
    end
    
    # Uniform in range
    def self.uniform(min: -1, max: 1)
      min + rand * (max - min)
    end
    
    # Lévy flight (power-law jumps)
    def self.levy(alpha: 1.5, scale: 1.0)
      # Mantegna's algorithm for Lévy stable
      u = rand * Math::PI - Math::PI / 2
      v = -Math.log(rand)
      
      scale * Math.sin(alpha * u) / (Math.cos(u) ** (1.0 / alpha)) *
        (Math.cos((1 - alpha) * u) / v) ** ((1 - alpha) / alpha)
    rescue
      0  # Fallback for numerical issues
    end
    
    # Logistic map chaos
    def self.logistic(x, r: 3.99)
      r * x * (1 - x)
    end
    
    # Lorenz attractor (3D chaos, return one coord)
    class LorenzAttractor
      def initialize(sigma: 10, rho: 28, beta: 8.0/3)
        @sigma, @rho, @beta = sigma, rho, beta
        @x, @y, @z = rand, rand, rand
        @dt = 0.01
      end
      
      def step
        dx = @sigma * (@y - @x)
        dy = @x * (@rho - @z) - @y
        dz = @x * @y - @beta * @z
        
        @x += dx * @dt
        @y += dy * @dt
        @z += dz * @dt
        
        [@x, @y, @z]
      end
      
      def next_value(coord: :x)
        step
        case coord
        when :x then @x / 20.0  # Normalize roughly to [-1, 1]
        when :y then @y / 30.0
        when :z then (@z - 25) / 20.0
        end
      end
    end
    
    # Henon map (2D chaos)
    class HenonMap
      def initialize(a: 1.4, b: 0.3)
        @a, @b = a, b
        @x, @y = rand * 0.1, rand * 0.1
      end
      
      def step
        x_new = 1 - @a * @x**2 + @y
        y_new = @b * @x
        @x, @y = x_new, y_new
        [@x, @y]
      end
      
      def next_value
        step
        @x.clamp(-1.5, 1.5) / 1.5  # Normalize
      end
    end
    
    # Drunk walk (Brownian motion with memory)
    class DrunkWalk
      def initialize(step_size: 0.1, bounds: [-1, 1])
        @step_size = step_size
        @bounds = bounds
        @position = 0
      end
      
      def step
        @position += (rand - 0.5) * 2 * @step_size
        @position = @position.clamp(*@bounds)
      end
      
      def next_value
        step
        @position
      end
      
      def reset
        @position = 0
      end
    end
    
    # Perlin-like smooth noise
    class SmoothNoise
      def initialize(frequency: 0.1)
        @frequency = frequency
        @phase = rand * 1000
        @time = 0
      end
      
      def next_value
        @time += @frequency
        # Simplified smooth noise using sin superposition
        (Math.sin(@time + @phase) * 0.5 +
         Math.sin(@time * 2.1 + @phase * 1.3) * 0.3 +
         Math.sin(@time * 4.7 + @phase * 0.7) * 0.2)
      end
    end
  end
  
  # ============================================================================
  # DERANGEMENT CONFIGURATIONS
  # Define how each degree of freedom can be perturbed
  # ============================================================================
  
  class DerangementConfig
    attr_accessor :pitch, :duration, :amplitude, :onset, :structure, :meta
    
    def initialize(
      pitch: nil,
      duration: nil, 
      amplitude: nil,
      onset: nil,
      structure: nil,
      meta: nil
    )
      @pitch = pitch || PitchDerangement.new
      @duration = duration || DurationDerangement.new
      @amplitude = amplitude || AmplitudeDerangement.new
      @onset = onset || OnsetDerangement.new
      @structure = structure || StructureDerangement.new
      @meta = meta || MetaDerangement.new
    end
    
    # Preset configurations
    def self.subtle
      new(
        pitch: PitchDerangement.new(enabled: true, intensity: 0.1),
        duration: DurationDerangement.new(enabled: true, intensity: 0.1),
        amplitude: AmplitudeDerangement.new(enabled: true, intensity: 0.1),
        onset: OnsetDerangement.new(enabled: false),
        structure: StructureDerangement.new(enabled: false),
        meta: MetaDerangement.new(enabled: false)
      )
    end
    
    def self.moderate
      new(
        pitch: PitchDerangement.new(enabled: true, intensity: 0.3, strategy: :gaussian),
        duration: DurationDerangement.new(enabled: true, intensity: 0.3),
        amplitude: AmplitudeDerangement.new(enabled: true, intensity: 0.3),
        onset: OnsetDerangement.new(enabled: true, intensity: 0.2),
        structure: StructureDerangement.new(enabled: true, swap_probability: 0.1),
        meta: MetaDerangement.new(enabled: false)
      )
    end
    
    def self.chaotic
      new(
        pitch: PitchDerangement.new(enabled: true, intensity: 0.6, strategy: :levy),
        duration: DurationDerangement.new(enabled: true, intensity: 0.5, strategy: :chaotic),
        amplitude: AmplitudeDerangement.new(enabled: true, intensity: 0.5),
        onset: OnsetDerangement.new(enabled: true, intensity: 0.4),
        structure: StructureDerangement.new(enabled: true, swap_probability: 0.3, reverse_probability: 0.1),
        meta: MetaDerangement.new(enabled: true, intensity_drift: 0.1)
      )
    end
    
    def self.maximum
      new(
        pitch: PitchDerangement.new(
          enabled: true, intensity: 1.0, strategy: :multi,
          strategies: [:gaussian, :levy, :chaotic, :brownian],
          microtonal: true, octave_displacement: true
        ),
        duration: DurationDerangement.new(
          enabled: true, intensity: 1.0, strategy: :multi,
          allow_zero: false, allow_extreme: true
        ),
        amplitude: AmplitudeDerangement.new(
          enabled: true, intensity: 1.0, strategy: :multi,
          allow_silence: true, allow_clip: false
        ),
        onset: OnsetDerangement.new(
          enabled: true, intensity: 1.0,
          allow_negative: true, allow_overlap: true
        ),
        structure: StructureDerangement.new(
          enabled: true, swap_probability: 0.5,
          reverse_probability: 0.2, skip_probability: 0.1,
          repeat_probability: 0.15, nest_probability: 0.1
        ),
        meta: MetaDerangement.new(
          enabled: true, intensity_drift: 0.3,
          strategy_mutation: true, self_modification: true
        )
      )
    end
  end
  
  # ============================================================================
  # PITCH DERANGEMENT
  # ============================================================================
  
  class PitchDerangement
    attr_accessor :enabled, :intensity, :strategy, :strategies,
                  :microtonal, :octave_displacement, :scale_lock, :range
    
    def initialize(
      enabled: true,
      intensity: 0.3,
      strategy: :gaussian,
      strategies: nil,
      microtonal: false,
      octave_displacement: false,
      scale_lock: nil,  # e.g., [0, 2, 4, 5, 7, 9, 11] for major
      range: [24, 96]
    )
      @enabled = enabled
      @intensity = intensity
      @strategy = strategy
      @strategies = strategies
      @microtonal = microtonal
      @octave_displacement = octave_displacement
      @scale_lock = scale_lock
      @range = range
      
      @chaos_sources = {
        lorenz: EntropySources::LorenzAttractor.new,
        henon: EntropySources::HenonMap.new,
        drunk: EntropySources::DrunkWalk.new(step_size: 0.2),
        smooth: EntropySources::SmoothNoise.new(frequency: 0.05)
      }
    end
    
    def derange(pitch)
      return pitch unless @enabled
      
      deviation = case active_strategy
        when :gaussian
          EntropySources.gaussian(stddev: 6 * @intensity)
        when :uniform
          EntropySources.uniform(min: -12 * @intensity, max: 12 * @intensity)
        when :levy
          EntropySources.levy(scale: 4 * @intensity).clamp(-24, 24)
        when :chaotic
          @chaos_sources[:lorenz].next_value * 12 * @intensity
        when :brownian
          @chaos_sources[:drunk].next_value * 12 * @intensity
        when :smooth
          @chaos_sources[:smooth].next_value * 6 * @intensity
        when :multi
          # Blend multiple strategies
          selected = (@strategies || [:gaussian, :levy]).sample
          derange_with_strategy(pitch, selected) - pitch
        else
          0
        end
      
      new_pitch = pitch + deviation
      
      # Octave displacement
      if @octave_displacement && rand < @intensity * 0.3
        new_pitch += [-24, -12, 12, 24].sample
      end
      
      # Microtonal (return float)
      unless @microtonal
        new_pitch = new_pitch.round
      end
      
      # Scale lock
      if @scale_lock
        pc = new_pitch.round % 12
        unless @scale_lock.include?(pc)
          # Snap to nearest scale degree
          closest = @scale_lock.min_by { |s| (s - pc).abs % 12 }
          new_pitch = (new_pitch.round / 12) * 12 + closest
        end
      end
      
      # Range clamp
      new_pitch.clamp(*@range)
    end
    
    def derange_chord(pitches)
      return pitches unless @enabled
      pitches.map { |p| derange(p) }
    end
    
    private
    
    def active_strategy
      @strategies ? @strategies.sample : @strategy
    end
    
    def derange_with_strategy(pitch, strat)
      old_strategy = @strategy
      @strategy = strat
      result = derange(pitch)
      @strategy = old_strategy
      result
    end
  end
  
  # ============================================================================
  # DURATION DERANGEMENT
  # ============================================================================
  
  class DurationDerangement
    attr_accessor :enabled, :intensity, :strategy, :allow_zero, :allow_extreme,
                  :min_duration, :max_duration, :quantize
    
    def initialize(
      enabled: true,
      intensity: 0.3,
      strategy: :gaussian,
      allow_zero: false,
      allow_extreme: false,
      min_duration: 0.01,
      max_duration: 8.0,
      quantize: nil  # e.g., 0.0625 for 16th notes
    )
      @enabled = enabled
      @intensity = intensity
      @strategy = strategy
      @allow_zero = allow_zero
      @allow_extreme = allow_extreme
      @min_duration = min_duration
      @max_duration = max_duration
      @quantize = quantize
      
      @chaos = EntropySources::HenonMap.new
    end
    
    def derange(duration)
      return duration unless @enabled
      
      multiplier = case @strategy
        when :gaussian
          1.0 + EntropySources.gaussian(stddev: 0.5 * @intensity)
        when :uniform
          1.0 + EntropySources.uniform(min: -0.5 * @intensity, max: 0.5 * @intensity)
        when :levy
          1.0 + EntropySources.levy(scale: 0.3 * @intensity).clamp(-0.8, 2.0)
        when :chaotic
          1.0 + @chaos.next_value * @intensity
        when :exponential
          # Favor shorter durations
          2 ** (EntropySources.gaussian(stddev: @intensity) - @intensity / 2)
        when :multi
          # Random strategy per call
          strategies = [:gaussian, :uniform, :exponential]
          old_strat = @strategy
          @strategy = strategies.sample
          result = derange(duration) / duration
          @strategy = old_strat
          result
        else
          1.0
        end
      
      new_duration = duration * multiplier.abs
      
      # Extreme values
      if @allow_extreme && rand < @intensity * 0.1
        new_duration *= [0.1, 0.25, 4.0, 8.0].sample
      end
      
      # Quantize
      if @quantize
        new_duration = (new_duration / @quantize).round * @quantize
      end
      
      # Clamp
      min = @allow_zero ? 0 : @min_duration
      new_duration.clamp(min, @max_duration)
    end
  end
  
  # ============================================================================
  # AMPLITUDE DERANGEMENT
  # ============================================================================
  
  class AmplitudeDerangement
    attr_accessor :enabled, :intensity, :strategy, :allow_silence, :allow_clip,
                  :dynamics_curve
    
    def initialize(
      enabled: true,
      intensity: 0.3,
      strategy: :gaussian,
      allow_silence: false,
      allow_clip: false,
      dynamics_curve: :linear  # :linear, :exponential, :logarithmic
    )
      @enabled = enabled
      @intensity = intensity
      @strategy = strategy
      @allow_silence = allow_silence
      @allow_clip = allow_clip
      @dynamics_curve = dynamics_curve
      
      @smooth = EntropySources::SmoothNoise.new(frequency: 0.1)
    end
    
    def derange(amplitude)
      return amplitude unless @enabled
      
      deviation = case @strategy
        when :gaussian
          EntropySources.gaussian(stddev: 0.3 * @intensity)
        when :uniform
          EntropySources.uniform(min: -0.5 * @intensity, max: 0.5 * @intensity)
        when :smooth
          @smooth.next_value * 0.4 * @intensity
        when :spiky
          # Occasional loud spikes
          rand < 0.1 * @intensity ? rand * 0.5 : EntropySources.gaussian(stddev: 0.1 * @intensity)
        when :multi
          [:gaussian, :smooth, :spiky].sample
          # Recursive but with different strategy
          old = @strategy
          @strategy = [:gaussian, :smooth].sample
          result = derange(amplitude) - amplitude
          @strategy = old
          result
        else
          0
        end
      
      new_amp = amplitude + deviation
      
      # Apply dynamics curve
      new_amp = case @dynamics_curve
        when :exponential
          new_amp ** 1.5
        when :logarithmic
          new_amp > 0 ? Math.log(1 + new_amp * 10) / Math.log(11) : 0
        else
          new_amp
        end
      
      # Silence
      if @allow_silence && rand < @intensity * 0.1
        return 0
      end
      
      # Clamp
      max = @allow_clip ? 1.5 : 1.0
      min = @allow_silence ? 0 : 0.01
      new_amp.clamp(min, max)
    end
  end
  
  # ============================================================================
  # ONSET DERANGEMENT (timing)
  # ============================================================================
  
  class OnsetDerangement
    attr_accessor :enabled, :intensity, :allow_negative, :allow_overlap,
                  :max_shift, :swing_amount
    
    def initialize(
      enabled: true,
      intensity: 0.2,
      allow_negative: false,
      allow_overlap: false,
      max_shift: 0.5,
      swing_amount: 0  # 0-1, affects even-numbered events
    )
      @enabled = enabled
      @intensity = intensity
      @allow_negative = allow_negative
      @allow_overlap = allow_overlap
      @max_shift = max_shift
      @swing_amount = swing_amount
      
      @drunk = EntropySources::DrunkWalk.new(step_size: 0.1)
    end
    
    def derange(onset, event_index: 0)
      return onset unless @enabled
      
      shift = @drunk.next_value * @max_shift * @intensity
      
      # Swing (delays even events)
      if @swing_amount > 0 && event_index.even?
        shift += @swing_amount * 0.1
      end
      
      new_onset = onset + shift
      
      # Negative check
      new_onset = [new_onset, 0].max unless @allow_negative
      
      new_onset
    end
  end
  
  # ============================================================================
  # STRUCTURE DERANGEMENT
  # ============================================================================
  
  class StructureDerangement
    attr_accessor :enabled, :swap_probability, :reverse_probability,
                  :skip_probability, :repeat_probability, :nest_probability
    
    def initialize(
      enabled: true,
      swap_probability: 0.1,
      reverse_probability: 0.05,
      skip_probability: 0.05,
      repeat_probability: 0.1,
      nest_probability: 0.05
    )
      @enabled = enabled
      @swap_probability = swap_probability
      @reverse_probability = reverse_probability
      @skip_probability = skip_probability
      @repeat_probability = repeat_probability
      @nest_probability = nest_probability
    end
    
    def derange_sequence(events)
      return events unless @enabled
      return events if events.empty?
      
      result = events.dup
      
      # Random swaps
      if rand < @swap_probability
        i, j = rand(result.length), rand(result.length)
        result[i], result[j] = result[j], result[i]
      end
      
      # Reverse segments
      if rand < @reverse_probability
        start = rand(result.length)
        len = rand(2..[result.length - start, 5].min)
        result[start, len] = result[start, len].reverse
      end
      
      # Skip events
      if rand < @skip_probability
        result = result.reject { rand < 0.2 }
      end
      
      # Repeat events
      if rand < @repeat_probability
        idx = rand(result.length)
        repeats = rand(1..3)
        result.insert(idx, *([result[idx]] * repeats))
      end
      
      result
    end
    
    # Derange nested Free monad structure
    def derange_pattern(pattern)
      return pattern unless @enabled
      return pattern if pattern.pure?
      
      instruction = pattern.instruction
      
      case instruction
      when FreeMonad::Sequence
        actions = instruction.actions
        
        # Apply structural derangements
        actions = derange_sequence(actions)
        
        # Recursively derange children
        actions = actions.map { |a| derange_pattern(a) }
        
        FreeMonad::Suspend.new(FreeMonad::Sequence.new(actions))
        
      when FreeMonad::Parallel
        voices = instruction.voices
        
        # Possibly swap voices
        if rand < @swap_probability * 2
          voices = voices.shuffle
        end
        
        voices = voices.map { |v| derange_pattern(v) }
        FreeMonad::Suspend.new(FreeMonad::Parallel.new(voices))
        
      else
        pattern
      end
    end
  end
  
  # ============================================================================
  # META DERANGEMENT (the parameters derange themselves)
  # ============================================================================
  
  class MetaDerangement
    attr_accessor :enabled, :intensity_drift, :strategy_mutation, :self_modification
    
    def initialize(
      enabled: false,
      intensity_drift: 0.1,
      strategy_mutation: false,
      self_modification: false
    )
      @enabled = enabled
      @intensity_drift = intensity_drift
      @strategy_mutation = strategy_mutation
      @self_modification = self_modification
      
      @drift_walk = EntropySources::DrunkWalk.new(step_size: 0.05, bounds: [-0.5, 0.5])
    end
    
    def apply_to_config!(config)
      return unless @enabled
      
      # Drift all intensities
      if @intensity_drift > 0
        drift = @drift_walk.next_value * @intensity_drift
        
        config.pitch.intensity = (config.pitch.intensity + drift).clamp(0, 1)
        config.duration.intensity = (config.duration.intensity + drift * 0.8).clamp(0, 1)
        config.amplitude.intensity = (config.amplitude.intensity + drift * 0.6).clamp(0, 1)
      end
      
      # Mutate strategies
      if @strategy_mutation && rand < 0.1
        strategies = [:gaussian, :uniform, :levy, :chaotic, :brownian, :smooth]
        config.pitch.strategy = strategies.sample
        config.duration.strategy = [:gaussian, :uniform, :exponential, :chaotic].sample
      end
      
      # Self-modification: change meta parameters
      if @self_modification && rand < 0.05
        @intensity_drift = (@intensity_drift + (rand - 0.5) * 0.1).clamp(0, 0.5)
      end
    end
  end
  
  # ============================================================================
  # DERANGING INTERPRETER
  # Wraps the standard interpreter with derangement
  # ============================================================================
  
  class DerangingInterpreter
    attr_reader :config, :events, :stats
    
    def initialize(config = DerangementConfig.maximum)
      @config = config
      @events = []
      @stats = { total: 0, pitch_changes: 0, duration_changes: 0, structural_changes: 0 }
    end
    
    def interpret(pattern, matter, current_beat = 0)
      # Apply meta derangement to evolve config
      @config.meta.apply_to_config!(@config)
      
      # Possibly derange the pattern structure first
      pattern = @config.structure.derange_pattern(pattern)
      
      interpret_recursive(pattern, matter, current_beat)
    end
    
    private
    
    def interpret_recursive(pattern, matter, current_beat)
      return current_beat if pattern.pure?
      
      instruction = pattern.instruction
      
      case instruction
      when FreeMonad::Sequence
        beat = current_beat
        instruction.actions.each do |action|
          beat = interpret_recursive(action, matter, beat)
        end
        beat
        
      when FreeMonad::Parallel
        max_beat = current_beat
        instruction.voices.each do |voice|
          end_beat = interpret_recursive(voice, matter, current_beat)
          max_beat = [max_beat, end_beat].max
        end
        max_beat
        
      when FreeMonad::PlayNote
        emit_note(instruction, matter, current_beat)
        
      when FreeMonad::PlayChord
        emit_chord(instruction, matter, current_beat)
        
      when FreeMonad::Rest
        deranged_dur = @config.duration.derange(instruction.duration)
        @events << { type: :rest, at: current_beat, dur: deranged_dur }
        current_beat + deranged_dur
        
      else
        current_beat
      end
    end
    
    def emit_note(instruction, matter, beat)
      @stats[:total] += 1
      
      orig_pitch = instruction.pitch
      orig_dur = instruction.duration
      orig_amp = instruction.amplitude
      
      # Derange everything
      deranged_pitch = @config.pitch.derange(orig_pitch)
      deranged_dur = @config.duration.derange(orig_dur)
      deranged_amp = @config.amplitude.derange(orig_amp)
      deranged_onset = @config.onset.derange(beat, event_index: @stats[:total])
      
      # Track stats
      @stats[:pitch_changes] += 1 if (deranged_pitch - orig_pitch).abs > 0.5
      @stats[:duration_changes] += 1 if (deranged_dur - orig_dur).abs > 0.05
      
      @events << {
        type: :note,
        at: deranged_onset,
        dur: deranged_dur,
        pitch: deranged_pitch,
        amplitude: deranged_amp,
        original: { pitch: orig_pitch, dur: orig_dur, amp: orig_amp }
      }
      
      beat + deranged_dur
    end
    
    def emit_chord(instruction, matter, beat)
      @stats[:total] += 1
      
      orig_pitches = instruction.pitches
      orig_dur = instruction.duration
      orig_amp = instruction.amplitude
      
      deranged_pitches = @config.pitch.derange_chord(orig_pitches)
      deranged_dur = @config.duration.derange(orig_dur)
      deranged_amp = @config.amplitude.derange(orig_amp)
      deranged_onset = @config.onset.derange(beat, event_index: @stats[:total])
      
      @events << {
        type: :chord,
        at: deranged_onset,
        dur: deranged_dur,
        pitches: deranged_pitches,
        amplitude: deranged_amp,
        original: { pitches: orig_pitches, dur: orig_dur, amp: orig_amp }
      }
      
      beat + deranged_dur
    end
    
    def events_to_score
      @events.reject { |e| e[:type] == :rest }.map do |e|
        pitches = e[:pitches] || [e[:pitch]]
        {
          id: "deranged-#{e[:at].round(3)}",
          at: e[:at],
          dur: e[:dur],
          world_object: { world: :pitch_space, type: :note, value: pitches },
          audio: {
            frequencies: pitches.map { |p| midi_to_hz(p) },
            amplitude: e[:amplitude],
            synth: 'sine'
          },
          meta: { deranged: true, original: e[:original] }
        }
      end
    end
    
    def midi_to_hz(midi)
      440.0 * (2.0 ** ((midi - 69) / 12.0))
    end
    
    public :events_to_score
  end
  
  # ============================================================================
  # PATTERN DERANGERS
  # Apply maximum dynamism to existing patterns
  # ============================================================================
  
  module PatternDerangers
    extend FreeMonad::DSL
    
    # Derange any pattern with specified config
    def self.derange(pattern, config: DerangementConfig.maximum, matter: nil)
      matter ||= default_matter
      
      interpreter = DerangingInterpreter.new(config)
      interpreter.interpret(pattern, matter)
      
      {
        events: interpreter.events_to_score,
        stats: interpreter.stats,
        config: config
      }
    end
    
    # Maximum dynamism Aphex Twin
    def self.maximum_aphex(duration: 8.0)
      base = QuantumAphexAutechre::AphexTwinPatterns.drill_n_bass(duration: duration, intensity: 0.8)
      derange(base, config: aphex_config)
    end
    
    # Maximum dynamism Autechre
    def self.maximum_autechre(duration: 8.0)
      base = QuantumAphexAutechre::AutechrePatterns.generative_rhythm(duration: duration)
      derange(base, config: autechre_config)
    end
    
    # Configuration presets for artists
    def self.aphex_config
      DerangementConfig.new(
        pitch: PitchDerangement.new(
          enabled: true, intensity: 0.7, strategy: :multi,
          strategies: [:gaussian, :levy, :chaotic],
          microtonal: true, octave_displacement: true
        ),
        duration: DurationDerangement.new(
          enabled: true, intensity: 0.8, strategy: :exponential,
          allow_extreme: true, min_duration: 0.01
        ),
        amplitude: AmplitudeDerangement.new(
          enabled: true, intensity: 0.6, strategy: :spiky
        ),
        onset: OnsetDerangement.new(
          enabled: true, intensity: 0.5, swing_amount: 0.3
        ),
        structure: StructureDerangement.new(
          enabled: true, swap_probability: 0.3,
          repeat_probability: 0.4, skip_probability: 0.1
        ),
        meta: MetaDerangement.new(
          enabled: true, intensity_drift: 0.2, strategy_mutation: true
        )
      )
    end
    
    def self.autechre_config
      DerangementConfig.new(
        pitch: PitchDerangement.new(
          enabled: true, intensity: 0.5, strategy: :brownian,
          microtonal: false, octave_displacement: false
        ),
        duration: DurationDerangement.new(
          enabled: true, intensity: 0.9, strategy: :chaotic,
          allow_extreme: true, quantize: nil  # No quantization
        ),
        amplitude: AmplitudeDerangement.new(
          enabled: true, intensity: 0.4, strategy: :smooth
        ),
        onset: OnsetDerangement.new(
          enabled: true, intensity: 0.7, allow_overlap: true
        ),
        structure: StructureDerangement.new(
          enabled: true, swap_probability: 0.2,
          reverse_probability: 0.15, nest_probability: 0.1
        ),
        meta: MetaDerangement.new(
          enabled: true, intensity_drift: 0.15, self_modification: true
        )
      )
    end
    
    private
    
    def self.default_matter
      { beat: 0, tempo: 120 }
    end
  end
  
  # ============================================================================
  # SHOWCASE: MAXIMUM DYNAMISM PATTERNS
  # ============================================================================
  
  class Showcase
    extend FreeMonad::DSL
    
    def self.maximum_dynamism_demo
      sequence!(
        section_marker("╔══════════════════════════════════════╗"),
        section_marker("║     MAXIMUM DYNAMISM SHOWCASE        ║"),
        section_marker("║  Every DOF Derangeable with Entropy  ║"),
        section_marker("╚══════════════════════════════════════╝"),
        rest!(0.5),
        
        section_marker("=== SUBTLE DERANGEMENT ==="),
        build_deranged_pattern(:subtle),
        rest!(0.5),
        
        section_marker("=== MODERATE CHAOS ==="),
        build_deranged_pattern(:moderate),
        rest!(0.5),
        
        section_marker("=== FULL CHAOS ==="),
        build_deranged_pattern(:chaotic),
        rest!(0.5),
        
        section_marker("=== MAXIMUM DYNAMISM ==="),
        build_deranged_pattern(:maximum),
        rest!(0.5),
        
        section_marker("=== APHEX MAXIMUM ==="),
        QuantumAphexAutechre::AphexTwinPatterns.drill_n_bass(duration: 4.0, intensity: 0.9),
        rest!(0.5),
        
        section_marker("=== AUTECHRE MAXIMUM ==="),
        QuantumAphexAutechre::AutechrePatterns.quantum_rhythm(duration: 4.0)
      )
    end
    
    private
    
    def self.section_marker(name)
      FreeMonad::Pure.new(name)
    end
    
    def self.build_deranged_pattern(level)
      # Build a base pattern
      base = sequence!(
        play_note!(60, 0.5, 0.4),
        play_note!(64, 0.5, 0.4),
        play_note!(67, 0.5, 0.4),
        play_chord!([60, 64, 67], 1.0, 0.5),
        rest!(0.25),
        play_note!(72, 0.25, 0.3),
        play_note!(71, 0.25, 0.3),
        play_note!(67, 0.25, 0.3),
        play_note!(60, 1.0, 0.4)
      )
      
      # The derangement happens at interpretation time
      # Mark it with the level for the runner
      FreeMonad::Suspend.new(
        FreeMonad::Transform.new(:derange, { pattern: base, level: level }) do |result|
          result || base
        end
      )
    end
  end
end
