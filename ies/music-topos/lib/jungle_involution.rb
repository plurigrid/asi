# lib/jungle_involution.rb
#
# INDUSTRIAL JUNGLE SELF-INVOLUTION
# ι: UIState → UIState where ι∘ι approaches id (fixed point)
#
# ============================================================================
# JUNGLE/DnB TEMPO DYNAMICS
# ============================================================================
#
# Standard tempo is WRONG. Jungle operates on:
# - Base tempo: 160-180 BPM
# - Half-time feel on bass: 80-90 BPM polyrhythm
# - Breakbeat subdivisions: 32nd notes, triplets, quintuplets SIMULTANEOUSLY
# - Tempo drift: ±5% continuous modulation
# - Time-stretching artifacts: pitch-independent tempo warping
#
# The beat is NEVER on the grid. The grid is a lie.
#
# ============================================================================
# SELF-INVOLUTION ARCHITECTURE
# ============================================================================
#
#   UIState_n → TRIFURCATE → [EXPAND, MUTATE, TRANSPOSE]
#                    ↓
#              EVALUATE each
#                    ↓
#              ARGMAX select
#                    ↓
#              UIState_{n+1}
#                    ↓
#              ι∘ι = id? → Fixed Point
#
# ============================================================================

require_relative 'free_monad'
require_relative 'maximum_dynamism'

module JungleInvolution
  extend FreeMonad::DSL
  
  # ============================================================================
  # NON-STANDARD TEMPO ENGINE
  # ============================================================================
  
  class TempoField
    attr_reader :base_bpm, :current_bpm, :phase, :drift_rate
    
    def initialize(base_bpm: 172, drift_rate: 0.03)
      @base_bpm = base_bpm
      @current_bpm = base_bpm
      @drift_rate = drift_rate
      @phase = 0
      @chaos = MaximumDynamism::EntropySources::LorenzAttractor.new
      @drunk = MaximumDynamism::EntropySources::DrunkWalk.new(step_size: 0.02, bounds: [-0.08, 0.08])
    end
    
    def tick
      # Tempo is a FIELD, not a value
      # Lorenz attractor for macro drift
      chaos_mod = @chaos.next_value * @drift_rate
      
      # Drunk walk for micro-timing
      micro_drift = @drunk.next_value * 0.02
      
      # Sinusoidal "breathing"
      @phase += 0.01
      breath = Math.sin(@phase * 0.3) * 0.015
      
      @current_bpm = @base_bpm * (1 + chaos_mod + micro_drift + breath)
      @current_bpm.clamp(@base_bpm * 0.85, @base_bpm * 1.15)
    end
    
    def beat_duration
      60.0 / @current_bpm
    end
    
    # Polyrhythmic subdivisions
    def subdivisions
      # Jungle: simultaneous 2, 3, 4, 5, 7 subdivisions
      {
        straight: 1.0,
        double: 0.5,
        triple: 1.0 / 3,
        quad: 0.25,
        quint: 0.2,
        sept: 1.0 / 7,
        # Irrational
        phi: 1.0 / ((1 + Math.sqrt(5)) / 2),
        sqrt2: 1.0 / Math.sqrt(2)
      }
    end
    
    def random_subdivision
      subdivisions.values.sample * beat_duration
    end
  end
  
  # ============================================================================
  # BREAKBEAT GENERATOR
  # The Amen break is a LIE. Every break is unique.
  # ============================================================================
  
  class BreakbeatEngine
    # Classic jungle drum mapping (approximate)
    KICK = 36
    SNARE = 38
    CLOSED_HAT = 42
    OPEN_HAT = 46
    RIDE = 51
    CRASH = 49
    TOM_LOW = 45
    TOM_MID = 47
    TOM_HI = 50
    
    # Amen break pattern (as a seed, will be destroyed)
    AMEN_SEED = [
      [:kick, 0],
      [:hat, 0.25],
      [:snare, 0.5],
      [:hat, 0.75],
      [:kick, 1.0],
      [:hat, 1.25],
      [:snare, 1.5],
      [:kick, 1.75],
      [:kick, 2.0],
      [:hat, 2.25],
      [:snare, 2.5],
      [:hat, 2.5],
      [:kick, 2.75],
      [:hat, 3.0],
      [:snare, 3.5],
      [:hat, 3.75]
    ]
    
    def initialize(tempo_field)
      @tempo = tempo_field
      @current_pattern = AMEN_SEED.dup
      @chop_probability = 0.4
      @stutter_probability = 0.3
      @reverse_probability = 0.15
      @pitch_shift_range = -12..12
      @time_stretch_range = 0.5..2.0
    end
    
    def generate_bar
      events = []
      pattern = mangle_pattern(@current_pattern)
      
      pattern.each do |hit_type, time|
        @tempo.tick
        
        # Time stretch the hit position
        stretched_time = time * rand(@time_stretch_range)
        
        # Quantize to current tempo subdivision (or don't)
        if rand > 0.3
          subdiv = @tempo.random_subdivision
          stretched_time = (stretched_time / subdiv).round * subdiv
        end
        
        # Generate the hit
        pitch, amp, dur = hit_params(hit_type)
        
        # Stutter
        if rand < @stutter_probability
          stutters = rand(2..6)
          stutter_dur = dur / stutters
          stutters.times do |i|
            events << {
              time: stretched_time + i * stutter_dur * 0.7,
              pitch: pitch + (rand > 0.5 ? rand(-3..3) : 0),
              amp: amp * (1 - i * 0.12),
              dur: stutter_dur * 0.8
            }
          end
        else
          events << { time: stretched_time, pitch: pitch, amp: amp, dur: dur }
        end
      end
      
      # Add ghost notes
      rand(3..8).times do
        events << {
          time: rand * 4.0,
          pitch: [CLOSED_HAT, SNARE, TOM_MID].sample,
          amp: 0.05 + rand * 0.1,
          dur: 0.02 + rand * 0.05
        }
      end
      
      events.sort_by { |e| e[:time] }
    end
    
    private
    
    def mangle_pattern(pattern)
      result = pattern.dup
      
      # Chop: remove random hits
      result = result.select { rand > @chop_probability * 0.5 }
      
      # Shuffle segments
      if rand < 0.3
        segment_size = rand(2..4)
        result = result.each_slice(segment_size).to_a.shuffle.flatten(1)
      end
      
      # Reverse segments
      if rand < @reverse_probability && result.length > 2
        start = rand(result.length - 1)
        max_len = [result.length - start, 4].min
        len = rand(2..max_len) if max_len >= 2
        if len && len >= 2
          result[start, len] = result[start, len].reverse
        end
      end
      
      # Time warp
      result.map do |type, time|
        warp = 1.0 + (rand - 0.5) * 0.3
        [type, time * warp]
      end
    end
    
    def hit_params(type)
      case type
      when :kick
        [KICK + rand(-2..2), 0.5 + rand * 0.2, 0.1 + rand * 0.1]
      when :snare
        [SNARE + rand(-3..3), 0.45 + rand * 0.15, 0.08 + rand * 0.08]
      when :hat
        [[CLOSED_HAT, OPEN_HAT].sample, 0.15 + rand * 0.2, 0.02 + rand * 0.04]
      else
        [TOM_MID, 0.3, 0.05]
      end
    end
  end
  
  # ============================================================================
  # BASS ENGINE (Half-time, Sub-bass, Reese)
  # ============================================================================
  
  class BassEngine
    def initialize(tempo_field)
      @tempo = tempo_field
      @root = 36  # Low C
      @current_note = @root
      @movement_probability = 0.4
      @intervals = [-5, -3, 0, 2, 4, 7, 12]  # Dark intervals
    end
    
    def generate_bar
      events = []
      
      # Bass operates at HALF tempo
      half_beat = @tempo.beat_duration * 2
      
      # 2-4 bass hits per bar
      hits = rand(2..4)
      
      hits.times do |i|
        @tempo.tick
        
        time = i * (4.0 / hits) + (rand - 0.5) * 0.3
        
        # Occasional movement
        if rand < @movement_probability
          interval = @intervals.sample
          @current_note = (@root + interval).clamp(24, 48)
        end
        
        # Reese bass: slightly detuned unison
        detune = rand(0.02..0.08)
        
        events << {
          time: time,
          pitches: [@current_note, @current_note + detune, @current_note - detune],
          amp: 0.6 + rand * 0.2,
          dur: half_beat * (0.8 + rand * 0.4)
        }
        
        # Sub-bass hit
        if rand > 0.5
          events << {
            time: time,
            pitches: [@current_note - 12],
            amp: 0.4,
            dur: half_beat * 0.5
          }
        end
      end
      
      events
    end
  end
  
  # ============================================================================
  # UI STATE (Pattern state for evolution)
  # ============================================================================
  
  class UIState
    attr_accessor :break_pattern, :bass_pattern, :fx_params, :score, :generation
    
    def initialize(break_pattern: nil, bass_pattern: nil, fx_params: nil, generation: 0)
      @break_pattern = break_pattern || []
      @bass_pattern = bass_pattern || []
      @fx_params = fx_params || default_fx
      @score = 0.0
      @generation = generation
    end
    
    def default_fx
      {
        reverb: 0.3,
        delay_time: 0.375,  # Dotted 8th
        delay_feedback: 0.4,
        distortion: 0.2,
        filter_cutoff: 0.7,
        filter_resonance: 0.3
      }
    end
    
    def clone
      UIState.new(
        break_pattern: @break_pattern.map(&:dup),
        bass_pattern: @bass_pattern.map(&:dup),
        fx_params: @fx_params.dup,
        generation: @generation
      )
    end
    
    def to_events
      all = []
      
      @break_pattern.each do |e|
        all << {
          type: :drum,
          at: e[:time],
          dur: e[:dur],
          pitch: e[:pitch],
          amplitude: e[:amp]
        }
      end
      
      @bass_pattern.each do |e|
        all << {
          type: :bass,
          at: e[:time],
          dur: e[:dur],
          pitches: e[:pitches],
          amplitude: e[:amp]
        }
      end
      
      all.sort_by { |e| e[:at] }
    end
  end
  
  # ============================================================================
  # TRIFURCATION OPERATORS
  # ============================================================================
  
  module Trifurcate
    # EXPAND: Add more events, increase density
    def self.expand(state)
      new_state = state.clone
      new_state.generation += 1
      
      # Double some drum hits
      additions = []
      state.break_pattern.each do |e|
        if rand < 0.3
          offset = rand(0.02..0.1)
          additions << e.merge(time: e[:time] + offset, amp: e[:amp] * 0.7)
        end
      end
      new_state.break_pattern += additions
      
      # Add bass harmonics
      state.bass_pattern.each do |e|
        if rand < 0.4
          new_pitches = e[:pitches] + [e[:pitches].first + 12]
          additions << e.merge(pitches: new_pitches.uniq)
        end
      end
      
      # Intensify FX
      new_state.fx_params[:distortion] *= 1.2
      new_state.fx_params[:reverb] *= 0.9
      
      new_state
    end
    
    # MUTATE: Change existing events randomly
    def self.mutate(state)
      new_state = state.clone
      new_state.generation += 1
      
      # Mutate drum timing
      new_state.break_pattern = state.break_pattern.map do |e|
        if rand < 0.4
          e.merge(
            time: e[:time] + (rand - 0.5) * 0.2,
            pitch: e[:pitch] + rand(-5..5),
            amp: (e[:amp] * (0.7 + rand * 0.6)).clamp(0.05, 0.9)
          )
        else
          e.dup
        end
      end
      
      # Mutate bass
      new_state.bass_pattern = state.bass_pattern.map do |e|
        if rand < 0.3
          new_root = e[:pitches].first + [-5, -3, 2, 4, 7].sample
          e.merge(pitches: [new_root, new_root + 0.05, new_root - 0.05])
        else
          e.dup
        end
      end
      
      # Mutate FX
      new_state.fx_params.each do |k, v|
        if rand < 0.3
          new_state.fx_params[k] = (v + (rand - 0.5) * 0.2).clamp(0, 1)
        end
      end
      
      new_state
    end
    
    # TRANSPOSE: Shift pitch/time domains
    def self.transpose(state)
      new_state = state.clone
      new_state.generation += 1
      
      # Pitch transposition
      pitch_shift = [-12, -7, -5, 5, 7, 12].sample
      
      new_state.break_pattern = state.break_pattern.map do |e|
        e.merge(pitch: e[:pitch] + pitch_shift / 2)  # Drums: subtle shift
      end
      
      new_state.bass_pattern = state.bass_pattern.map do |e|
        e.merge(pitches: e[:pitches].map { |p| p + pitch_shift })
      end
      
      # Time transposition (phase shift)
      time_shift = rand * 0.5
      new_state.break_pattern.each { |e| e[:time] = (e[:time] + time_shift) % 4.0 }
      
      # Invert FX
      new_state.fx_params[:filter_cutoff] = 1.0 - state.fx_params[:filter_cutoff]
      
      new_state
    end
  end
  
  # ============================================================================
  # EVALUATION & SCORING
  # ============================================================================
  
  class Evaluator
    def initialize
      @intuition_bank = IntuitionBank.new
    end
    
    def evaluate(state)
      scores = {
        density: evaluate_density(state),
        syncopation: evaluate_syncopation(state),
        bass_power: evaluate_bass(state),
        chaos: evaluate_chaos(state),
        novelty: evaluate_novelty(state)
      }
      
      # Extract patterns for intuition mining
      patterns = extract_patterns(state)
      patterns.each { |p| @intuition_bank.record(p, scores.values.sum / scores.length) }
      
      # Weighted sum
      weights = { density: 0.2, syncopation: 0.3, bass_power: 0.2, chaos: 0.2, novelty: 0.1 }
      total = weights.sum { |k, w| scores[k] * w }
      
      state.score = total
      { total: total, components: scores, patterns: patterns }
    end
    
    private
    
    def evaluate_density(state)
      # More events = higher density score (up to a point)
      count = state.break_pattern.length + state.bass_pattern.length
      # Optimal: 30-60 events per bar
      if count < 15
        count / 30.0
      elsif count > 80
        1.0 - (count - 80) / 100.0
      else
        0.8 + (count - 30) / 150.0
      end
    end
    
    def evaluate_syncopation(state)
      # Measure off-grid-ness
      grid_positions = [0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 1.75, 2.0, 2.25, 2.5, 2.75, 3.0, 3.25, 3.5, 3.75]
      
      off_grid_count = state.break_pattern.count do |e|
        grid_positions.none? { |g| (e[:time] % 4.0 - g).abs < 0.05 }
      end
      
      # High syncopation = good
      (off_grid_count.to_f / [state.break_pattern.length, 1].max).clamp(0, 1)
    end
    
    def evaluate_bass(state)
      # Bass should be LOW and POWERFUL
      return 0.0 if state.bass_pattern.empty?
      
      avg_pitch = state.bass_pattern.flat_map { |e| e[:pitches] }.sum / 
                  state.bass_pattern.flat_map { |e| e[:pitches] }.length.to_f
      
      # Lower is better (optimal around 30-40)
      low_score = 1.0 - ((avg_pitch - 35).abs / 20.0).clamp(0, 1)
      
      # Amplitude should be high
      avg_amp = state.bass_pattern.sum { |e| e[:amp] } / state.bass_pattern.length.to_f
      
      low_score * 0.6 + avg_amp * 0.4
    end
    
    def evaluate_chaos(state)
      # Measure entropy/unpredictability
      times = state.break_pattern.map { |e| e[:time] }
      return 0.5 if times.length < 2
      
      intervals = times.each_cons(2).map { |a, b| b - a }
      
      # High variance = high chaos
      mean = intervals.sum / intervals.length.to_f
      variance = intervals.sum { |i| (i - mean) ** 2 } / intervals.length.to_f
      
      (variance * 5).clamp(0, 1)
    end
    
    def evaluate_novelty(state)
      # Compare to intuition bank
      patterns = extract_patterns(state)
      novelty_scores = patterns.map { |p| 1.0 - @intuition_bank.familiarity(p) }
      
      novelty_scores.empty? ? 0.5 : novelty_scores.sum / novelty_scores.length
    end
    
    def extract_patterns(state)
      patterns = []
      
      # Rhythmic pattern (quantized intervals)
      times = state.break_pattern.map { |e| e[:time] }.sort
      if times.length >= 3
        intervals = times.each_cons(2).map { |a, b| ((b - a) * 8).round / 8.0 }
        patterns << { type: :rhythm, data: intervals.first(8) }
      end
      
      # Pitch pattern
      pitches = state.break_pattern.map { |e| e[:pitch] % 12 }
      patterns << { type: :pitch_class, data: pitches.first(8) } if pitches.length >= 3
      
      # Bass movement
      bass_roots = state.bass_pattern.map { |e| e[:pitches].first % 12 }
      patterns << { type: :bass_movement, data: bass_roots } if bass_roots.length >= 2
      
      patterns
    end
  end
  
  # ============================================================================
  # INTUITION BANK (Pattern memory with decay)
  # ============================================================================
  
  class IntuitionBank
    def initialize(decay_rate: 0.95)
      @patterns = {}  # pattern_hash => { count:, success_rate:, last_seen: }
      @decay_rate = decay_rate
      @generation = 0
    end
    
    def record(pattern, score)
      key = pattern_hash(pattern)
      
      if @patterns[key]
        entry = @patterns[key]
        entry[:count] += 1
        entry[:success_rate] = entry[:success_rate] * 0.8 + score * 0.2
        entry[:last_seen] = @generation
      else
        @patterns[key] = { count: 1, success_rate: score, last_seen: @generation }
      end
    end
    
    def familiarity(pattern)
      key = pattern_hash(pattern)
      return 0.0 unless @patterns[key]
      
      entry = @patterns[key]
      age = @generation - entry[:last_seen]
      
      # Decay familiarity over time
      (entry[:count] / 10.0).clamp(0, 1) * (@decay_rate ** age)
    end
    
    def bias_for(pattern)
      key = pattern_hash(pattern)
      return 0.5 unless @patterns[key]
      
      @patterns[key][:success_rate]
    end
    
    def advance_generation
      @generation += 1
    end
    
    private
    
    def pattern_hash(pattern)
      pattern.hash
    end
  end
  
  # ============================================================================
  # SELF-INVOLUTION ENGINE
  # ι: UIState → UIState where ι∘ι → id (fixed point)
  # ============================================================================
  
  class SelfInvolution
    attr_reader :history, :intuition_bank
    
    def initialize(max_generations: 50, target_score: 0.85)
      @max_generations = max_generations
      @target_score = target_score
      @evaluator = Evaluator.new
      @intuition_bank = IntuitionBank.new
      @history = []
    end
    
    def evolve(initial_state)
      current = initial_state
      
      @max_generations.times do |gen|
        @intuition_bank.advance_generation
        
        # TRIFURCATE
        candidates = [
          { op: :expand, state: Trifurcate.expand(current) },
          { op: :mutate, state: Trifurcate.mutate(current) },
          { op: :transpose, state: Trifurcate.transpose(current) }
        ]
        
        # EVALUATE each
        evaluations = candidates.map do |c|
          eval_result = @evaluator.evaluate(c[:state])
          c.merge(evaluation: eval_result)
        end
        
        # ARGMAX select
        best = evaluations.max_by { |e| e[:evaluation][:total] }
        
        @history << {
          generation: gen,
          candidates: evaluations.map { |e| { op: e[:op], score: e[:evaluation][:total] } },
          selected: best[:op],
          score: best[:evaluation][:total]
        }
        
        current = best[:state]
        
        # FIXED POINT CHECK: ι∘ι = id?
        if best[:evaluation][:total] >= @target_score
          puts "  ✓ Fixed point reached at generation #{gen}"
          puts "    Score: #{best[:evaluation][:total].round(3)}"
          break
        end
        
        # Progress indicator
        if gen % 10 == 0
          puts "  Gen #{gen}: score=#{best[:evaluation][:total].round(3)} op=#{best[:op]}"
        end
      end
      
      current
    end
  end
  
  # ============================================================================
  # PATTERN BUILDER (Free Monad integration)
  # ============================================================================
  
  class JunglePatternBuilder
    extend FreeMonad::DSL
    
    def self.build(duration: 16.0, generations: 30)
      tempo_field = TempoField.new(base_bpm: 172)
      break_engine = BreakbeatEngine.new(tempo_field)
      bass_engine = BassEngine.new(tempo_field)
      
      # Generate initial state
      bars = (duration / 4.0).ceil
      initial_breaks = []
      initial_bass = []
      
      bars.times do |bar|
        bar_breaks = break_engine.generate_bar
        bar_breaks.each { |e| e[:time] += bar * 4.0 }
        initial_breaks += bar_breaks
        
        bar_bass = bass_engine.generate_bar
        bar_bass.each { |e| e[:time] += bar * 4.0 }
        initial_bass += bar_bass
      end
      
      initial_state = UIState.new(
        break_pattern: initial_breaks,
        bass_pattern: initial_bass
      )
      
      # Run self-involution
      puts "  Running self-involution (#{generations} generations max)..."
      involution = SelfInvolution.new(max_generations: generations, target_score: 0.8)
      evolved_state = involution.evolve(initial_state)
      
      # Convert to Free monad pattern
      state_to_pattern(evolved_state, tempo_field)
    end
    
    def self.state_to_pattern(state, tempo)
      events = state.to_events
      
      # Build sequence of play commands
      notes = events.map do |e|
        if e[:type] == :drum
          play_note!(e[:pitch].round, e[:dur], e[:amplitude])
        else
          pitches = e[:pitches].map(&:round)
          play_chord!(pitches, e[:dur], e[:amplitude])
        end
      end
      
      # Add rests between events
      sorted = events.sort_by { |e| e[:at] }
      with_rests = []
      last_time = 0
      
      sorted.each_with_index do |e, i|
        gap = e[:at] - last_time
        with_rests << rest!(gap) if gap > 0.01
        
        if e[:type] == :drum
          with_rests << play_note!(e[:pitch].round, e[:dur], e[:amplitude])
        else
          pitches = e[:pitches].map(&:round)
          with_rests << play_chord!(pitches, e[:dur], e[:amplitude])
        end
        
        last_time = e[:at] + e[:dur]
      end
      
      sequence!(*with_rests)
    end
  end
  
  # ============================================================================
  # SHOWCASE
  # ============================================================================
  
  class Showcase
    extend FreeMonad::DSL
    
    def self.jungle_involution_showcase
      sequence!(
        section_marker("╔══════════════════════════════════════╗"),
        section_marker("║   INDUSTRIAL JUNGLE SELF-INVOLUTION  ║"),
        section_marker("║  ι: UIState → UIState | ι∘ι → id    ║"),
        section_marker("╚══════════════════════════════════════╝"),
        rest!(0.3),
        
        section_marker("=== PHASE 1: Initial Breakbeat Chaos ==="),
        JunglePatternBuilder.build(duration: 8.0, generations: 15),
        rest!(0.5),
        
        section_marker("=== PHASE 2: Evolved Through Trifurcation ==="),
        JunglePatternBuilder.build(duration: 8.0, generations: 30),
        rest!(0.5),
        
        section_marker("=== PHASE 3: Fixed Point Convergence ==="),
        JunglePatternBuilder.build(duration: 8.0, generations: 50)
      )
    end
    
    def self.quick_jungle(duration: 4.0)
      JunglePatternBuilder.build(duration: duration, generations: 20)
    end
    
    private
    
    def self.section_marker(name)
      FreeMonad::Pure.new(name)
    end
  end
end
