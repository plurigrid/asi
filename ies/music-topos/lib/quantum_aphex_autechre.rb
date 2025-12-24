# lib/quantum_aphex_autechre.rb
#
# QUANTUM APHEX TWIN & QUANTUM AUTECHRE
# Categorical derivation of generative electronic music
#
# ============================================================================
# THEORETICAL FOUNDATIONS
# ============================================================================
#
# The key insight: Both artists work with NESTED TEMPORAL STRUCTURES and
# PROBABILITY-WEIGHTED DECISION TREES - exactly what Free/Cofree captures.
#
# Aphex Twin: Superposition of MULTIPLE METRIC GRIDS
#   - 4/4 pulse coexists with 7/8, 5/4, 11/8
#   - "Drill 'n' bass" = high-frequency sampling of breakbeat space
#   - Equation-derived melodies (Windowlicker formula speculation)
#   - The "creepy" quality = microtonal beating + uncanny valley timing
#
# Autechre: GENERATIVE GRAMMAR for rhythm and pitch
#   - Markov chains over rhythmic cells
#   - Cellular automata for parameter evolution  
#   - Max/MSP → categorical: objects = states, morphisms = transitions
#   - "Anti-groove" = rhythms in superposition that never fully collapse
#
# CATEGORICAL STRUCTURE:
#   Pattern (Free F) = Decision tree of possible musical events
#   Matter (Cofree G) = Environment that provides:
#     - Current metric position (polyrhythmic phase)
#     - Probability distributions for next events
#     - Accumulated history (for Markov transitions)
#     - Cellular automaton state
#
# The MODULE ACTION (Pattern ⊗ Matter → Events):
#   At each node, Matter "answers" Pattern's "question" by:
#   - Selecting from superposed options based on current state
#   - Applying probability weights from accumulated context
#   - Evolving internal state (CA step, Markov transition)
#
# ============================================================================

require_relative 'free_monad'

module QuantumAphexAutechre
  extend FreeMonad::DSL
  
  # ============================================================================
  # PART I: RHYTHMIC CATEGORY
  # Objects: Metric positions | Morphisms: Subdivisions & phase shifts
  # ============================================================================
  
  module RhythmCategory
    # POLYRHYTHMIC SUPERPOSITION
    # Key Aphex/Autechre technique: multiple metric grids simultaneously
    #
    # Mathematically: Given periods p₁, p₂, ..., pₙ
    # The superposition cycles with period LCM(p₁, ..., pₙ)
    # At each beat, we're at phase (t mod p₁, t mod p₂, ..., t mod pₙ)
    
    class PolymetricGrid
      attr_reader :periods, :accents
      
      def initialize(*periods, accents: nil)
        @periods = periods
        @accents = accents || periods.map { |p| [0] }  # Default: accent first beat
      end
      
      # Get the phase vector at time t
      def phase_at(t)
        @periods.map { |p| t % p }
      end
      
      # Is this an accent point in any grid?
      def accent_at?(t)
        phase = phase_at(t)
        phase.each_with_index.any? { |p, i| @accents[i].include?(p) }
      end
      
      # Interference pattern: how many grids align?
      def alignment_at(t)
        phase = phase_at(t)
        phase.each_with_index.count { |p, i| @accents[i].include?(p) }
      end
      
      # Full cycle length
      def period
        @periods.reduce(1) { |lcm, p| lcm.lcm(p) }
      end
      
      # Generate accent pattern for one full cycle
      def to_pattern
        (0...period).map { |t| alignment_at(t) }
      end
    end
    
    # EUCLIDEAN RHYTHMS (Toussaint)
    # Optimal distribution of k onsets in n positions
    # Related to Bresenham's line algorithm
    #
    # These appear throughout Aphex/Autechre as underlying pulse structures
    
    def self.euclidean(k, n, rotation: 0)
      return Array.new(n, false) if k.zero?
      return Array.new(n, true) if k >= n
      
      pattern = Array.new(n, false)
      step = n.to_f / k
      k.times { |i| pattern[((i * step) % n).floor] = true }
      pattern.rotate(rotation)
    end
    
    # METRIC MODULATION
    # Tempo relationship: new_tempo = old_tempo * (old_subdivision / new_subdivision)
    # This is Autechre's primary technique for "drifting" time
    
    def self.metric_modulation(old_tempo, old_subdiv, new_subdiv)
      old_tempo * (old_subdiv.to_f / new_subdiv)
    end
    
    # IRRATIONAL METERS (Nancarrow/Autechre)
    # Divisions that don't reduce to simple ratios
    # π/4 time, √2/4 time, etc.
    
    IRRATIONAL_RATIOS = {
      phi: (1 + Math.sqrt(5)) / 2,        # Golden ratio
      sqrt2: Math.sqrt(2),                 # √2
      pi_4: Math::PI / 4,                  # π/4
      e_3: Math::E / 3                     # e/3
    }
    
    def self.irrational_duration(base_duration, ratio_name)
      base_duration * IRRATIONAL_RATIOS[ratio_name]
    end
  end
  
  # ============================================================================
  # PART II: PITCH CATEGORY  
  # Objects: Pitch/frequency values | Morphisms: Intervals & transformations
  # ============================================================================
  
  module PitchCategory
    # EQUATION-DERIVED MELODIES (Aphex Twin speculation)
    # The Windowlicker/ΔMi−1 spectrograms suggest mathematical functions
    #
    # Approach: sample continuous functions, quantize to pitch space
    
    class EquationMelody
      def initialize(fn, sample_rate: 16, quantize: :chromatic)
        @fn = fn
        @sample_rate = sample_rate
        @quantize = quantize
      end
      
      def generate(duration)
        samples = (duration * @sample_rate).to_i
        (0...samples).map do |i|
          t = i.to_f / @sample_rate
          raw_pitch = @fn.call(t)
          quantize_pitch(raw_pitch)
        end
      end
      
      private
      
      def quantize_pitch(p)
        case @quantize
        when :chromatic
          p.round
        when :whole_tone
          (p / 2.0).round * 2
        when :microtonal
          (p * 4).round / 4.0  # Quarter-tones
        else
          p
        end
      end
    end
    
    # Specific equation types observed in Aphex Twin:
    APHEX_EQUATIONS = {
      # Spiral: logarithmic spiral in pitch space
      spiral: ->(t) { 60 + 12 * Math.log(1 + t) * Math.sin(t * Math::PI) },
      
      # Face: approximation of face-like spectrogram (simplified)
      face: ->(t) { 60 + 24 * Math.sin(t * 0.5) * Math.exp(-t * 0.1) },
      
      # Chaos: logistic map for unpredictable but deterministic melody
      logistic: ->(t, r: 3.7, x: 0.5) {
        x_next = x
        (t * 10).to_i.times { x_next = r * x_next * (1 - x_next) }
        36 + 48 * x_next
      },
      
      # Modular: modular arithmetic patterns (Selected Ambient Works II vibes)
      modular: ->(t, m: 7, b: 60) { b + ((t * 12).to_i % m) * 12 / m }
    }
    
    # SPECTRAL MORPHING (Autechre's granular/spectral approach)
    # Interpolate between harmonic series of different fundamentals
    
    def self.spectral_interpolation(freq1, freq2, blend, partials: 8)
      partials.times.map do |n|
        partial1 = freq1 * (n + 1)
        partial2 = freq2 * (n + 1)
        partial1 * (1 - blend) + partial2 * blend
      end
    end
    
    # PITCH DRIFT (Autechre: gradual detuning)
    # Model as random walk with bounds
    
    class PitchDrift
      def initialize(center, max_deviation: 0.5, step_size: 0.05)
        @center = center
        @max_deviation = max_deviation
        @step_size = step_size
        @current_offset = 0
      end
      
      def next_pitch
        @current_offset += (rand - 0.5) * @step_size * 2
        @current_offset = @current_offset.clamp(-@max_deviation, @max_deviation)
        @center + @current_offset
      end
      
      def reset
        @current_offset = 0
      end
    end
  end
  
  # ============================================================================
  # PART III: MARKOV PROCESSES
  # The stochastic backbone of Autechre's generative systems
  # ============================================================================
  
  module MarkovSystems
    # MARKOV CHAIN over musical cells
    # States: rhythmic/melodic cells | Transitions: probability matrix
    
    class MarkovChain
      attr_reader :states, :transitions, :current_state
      
      def initialize(states, transitions)
        @states = states
        @transitions = transitions  # Hash: state => [[next_state, probability], ...]
        @current_state = states.sample
      end
      
      def step
        probs = @transitions[@current_state] || []
        return @current_state if probs.empty?
        
        r = rand
        cumulative = 0
        probs.each do |next_state, prob|
          cumulative += prob
          if r <= cumulative
            @current_state = next_state
            return @current_state
          end
        end
        @current_state
      end
      
      def generate(n)
        n.times.map { step }
      end
    end
    
    # RHYTHMIC MARKOV CHAINS
    # Autechre-style: states are rhythmic cells, transitions based on "fit"
    
    def self.build_rhythmic_chain(cells, smoothness: 0.7)
      # smoothness: high = prefer similar cells, low = more random
      transitions = {}
      
      cells.each do |cell|
        cell_transitions = cells.map do |next_cell|
          # Calculate similarity (normalized edit distance or similar)
          similarity = cell_similarity(cell, next_cell)
          weight = smoothness * similarity + (1 - smoothness) * rand
          [next_cell, weight]
        end
        
        # Normalize to probabilities
        total = cell_transitions.sum { |_, w| w }
        transitions[cell] = cell_transitions.map { |c, w| [c, w / total] }
      end
      
      MarkovChain.new(cells, transitions)
    end
    
    def self.cell_similarity(a, b)
      return 1.0 if a == b
      return 0.0 if a.length != b.length
      
      matches = a.zip(b).count { |x, y| x == y }
      matches.to_f / a.length
    end
    
    # HIGHER-ORDER MARKOV (memory > 1)
    # Needed for Autechre's longer-range coherence
    
    class HigherOrderMarkov
      def initialize(order, states)
        @order = order
        @states = states
        @transitions = Hash.new { |h, k| h[k] = [] }
        @history = []
      end
      
      def train(sequence)
        sequence.each_cons(@order + 1) do |window|
          context = window[0...-1]
          next_state = window[-1]
          @transitions[context] << next_state
        end
      end
      
      def step
        if @history.length < @order
          next_state = @states.sample
        else
          context = @history.last(@order)
          candidates = @transitions[context]
          next_state = candidates.empty? ? @states.sample : candidates.sample
        end
        
        @history << next_state
        @history.shift if @history.length > @order * 2
        next_state
      end
    end
  end
  
  # ============================================================================
  # PART IV: CELLULAR AUTOMATA
  # Autechre's parameter evolution systems
  # ============================================================================
  
  module CellularAutomata
    # ELEMENTARY CA (Wolfram)
    # Rule 30, 110, etc. for pseudo-random but deterministic evolution
    
    class ElementaryCA
      attr_reader :state, :rule
      
      def initialize(size, rule: 30, seed: nil)
        @size = size
        @rule = rule
        @state = seed || Array.new(size) { rand > 0.5 }
        @state[@size / 2] = true if seed.nil?  # Single cell start
      end
      
      def step
        new_state = @size.times.map do |i|
          left = @state[(i - 1) % @size]
          center = @state[i]
          right = @state[(i + 1) % @size]
          
          pattern = (left ? 4 : 0) + (center ? 2 : 0) + (right ? 1 : 0)
          (@rule >> pattern) & 1 == 1
        end
        @state = new_state
      end
      
      def to_rhythm(true_value: 1, false_value: 0)
        @state.map { |s| s ? true_value : false_value }
      end
      
      def to_pitches(base: 60, step: 1)
        @state.each_with_index.select { |s, _| s }.map { |_, i| base + i * step }
      end
    end
    
    # 2D CA for more complex patterns (Game of Life, etc.)
    
    class GameOfLife
      def initialize(width, height, density: 0.3)
        @width = width
        @height = height
        @grid = Array.new(height) { Array.new(width) { rand < density } }
      end
      
      def step
        new_grid = Array.new(@height) { Array.new(@width) }
        
        @height.times do |y|
          @width.times do |x|
            neighbors = count_neighbors(x, y)
            alive = @grid[y][x]
            
            new_grid[y][x] = if alive
              neighbors == 2 || neighbors == 3
            else
              neighbors == 3
            end
          end
        end
        
        @grid = new_grid
      end
      
      def count_neighbors(x, y)
        count = 0
        (-1..1).each do |dy|
          (-1..1).each do |dx|
            next if dx == 0 && dy == 0
            nx = (x + dx) % @width
            ny = (y + dy) % @height
            count += 1 if @grid[ny][nx]
          end
        end
        count
      end
      
      def to_pitches(base: 36, x_step: 1, y_step: 12)
        pitches = []
        @height.times do |y|
          @width.times do |x|
            pitches << base + x * x_step + y * y_step if @grid[y][x]
          end
        end
        pitches
      end
      
      def population
        @grid.flatten.count(&:itself)
      end
    end
  end
  
  # ============================================================================
  # PART V: QUANTUM SUPERPOSITION PATTERNS
  # The core abstraction: patterns exist in superposition until "measured"
  # ============================================================================
  
  module QuantumPatterns
    # SUPERPOSITION STATE
    # A weighted collection of alternatives that collapse on measurement
    
    class Superposition
      attr_reader :states, :weights
      
      def initialize(states_with_weights)
        @states = states_with_weights.map(&:first)
        weights = states_with_weights.map(&:last)
        total = weights.sum
        @weights = weights.map { |w| w.to_f / total }
      end
      
      def measure
        r = rand
        cumulative = 0
        @weights.each_with_index do |w, i|
          cumulative += w
          return @states[i] if r <= cumulative
        end
        @states.last
      end
      
      def expected_value
        @states.zip(@weights).sum { |s, w| s * w }
      end
      
      # Interference: combine two superpositions
      def interfere(other, coupling: 0.5)
        combined_states = (@states + other.states).uniq
        combined_weights = combined_states.map do |s|
          w1 = @states.include?(s) ? @weights[@states.index(s)] : 0
          w2 = other.states.include?(s) ? other.weights[other.states.index(s)] : 0
          # Quantum-like interference (can be constructive or destructive)
          phase = rand * 2 * Math::PI
          (w1 + w2 * Math.cos(phase)).abs
        end
        Superposition.new(combined_states.zip(combined_weights))
      end
    end
    
    # ENTANGLED PARAMETERS
    # When one is measured, the other's distribution changes
    
    class EntangledPair
      def initialize(param_a_states, param_b_states, correlation_matrix)
        @a_states = param_a_states
        @b_states = param_b_states
        @correlations = correlation_matrix  # P(b|a)
        @measured_a = nil
      end
      
      def measure_a
        @measured_a = @a_states.sample
      end
      
      def measure_b
        return @b_states.sample unless @measured_a
        
        a_idx = @a_states.index(@measured_a)
        probs = @correlations[a_idx]
        
        r = rand
        cumulative = 0
        probs.each_with_index do |p, i|
          cumulative += p
          return @b_states[i] if r <= cumulative
        end
        @b_states.last
      end
      
      def reset
        @measured_a = nil
      end
    end
  end
  
  # ============================================================================
  # PART VI: PATTERN BUILDERS - APHEX TWIN
  # ============================================================================
  
  class AphexTwinPatterns
    extend FreeMonad::DSL
    
    # DRILL 'N' BASS: Hyper-fast breakbeat fragmentation
    # Key: very short durations, rapid alternation, occasional pauses
    
    def self.drill_n_bass(duration: 4.0, intensity: 0.8)
      events = []
      time = 0
      
      # Base: Amen break-style kick/snare positions
      kick_times = [0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5]
      snare_times = [0.25, 0.75, 1.25, 1.75, 2.25, 2.75, 3.25, 3.75]
      
      while time < duration
        # Fragment length varies based on intensity
        frag_length = intensity > rand ? rand(0.02..0.08) : rand(0.1..0.2)
        
        # Choose sound based on grid position
        is_kick = kick_times.any? { |kt| (time % 4.0 - kt).abs < 0.1 }
        is_snare = snare_times.any? { |st| (time % 4.0 - st).abs < 0.1 }
        
        pitch = if is_kick
          36 + rand(-2..2)
        elsif is_snare
          48 + rand(-3..3)  
        else
          [42, 44, 46, 50, 52].sample + rand(-1..1)  # Hi-hats, percussion
        end
        
        amp = is_kick ? 0.5 : (is_snare ? 0.4 : 0.15 + rand * 0.15)
        
        # Occasional glitch: repeat same hit rapidly
        if rand < intensity * 0.3
          repeats = rand(2..5)
          repeats.times do |r|
            events << play_note!(pitch + r, frag_length / repeats, amp * (1 - r * 0.15))
          end
        else
          events << play_note!(pitch, frag_length, amp)
        end
        
        # Occasional gap (the "breath" in drill 'n' bass)
        if rand < 0.1
          gap = rand(0.05..0.2)
          events << rest!(gap)
          time += gap
        end
        
        time += frag_length
      end
      
      sequence!(*events)
    end
    
    # AMBIENT DRIFT: Long evolving textures (SAW II style)
    # Key: slow modulation, microtonal beating, reverb-like overlap
    
    def self.ambient_drift(base: 48, duration: 16.0)
      events = []
      
      # Multiple layers with different periods
      layers = [
        { period: 8.0, pitches: [base, base + 7], amp: 0.25 },
        { period: 5.0, pitches: [base + 12, base + 19], amp: 0.15 },
        { period: 3.0, pitches: [base + 24], amp: 0.08 },
        { period: 13.0, pitches: [base - 12, base - 5], amp: 0.3 }
      ]
      
      # Create overlapping sustained tones
      layers.each do |layer|
        voice_events = []
        time = 0
        
        while time < duration
          # Slight pitch drift for beating
          pitches = layer[:pitches].map do |p|
            p + (rand - 0.5) * 0.1  # ±5 cents
          end
          
          hold = layer[:period] * (0.8 + rand * 0.4)
          
          voice_events << play_chord!(pitches.map(&:round), hold, layer[:amp])
          voice_events << rest!(layer[:period] * 0.1)  # Tiny gap
          
          time += layer[:period]
        end
        
        events << sequence!(*voice_events)
      end
      
      parallel!(*events)
    end
    
    # PREPARED PIANO: Acoustic-electronic hybrid (Drukqs style)
    # Key: mechanical sounds, string resonance, unexpected timbres
    
    def self.prepared_piano(duration: 8.0)
      events = []
      time = 0
      
      # "Prepared" sounds: muted, harmonics, string scrapes
      preparations = [
        { pitch_offset: 0, dur_mult: 1.0, amp: 0.4 },      # Normal
        { pitch_offset: 12, dur_mult: 0.3, amp: 0.15 },    # Harmonic
        { pitch_offset: 0.5, dur_mult: 2.0, amp: 0.1 },    # Muted/detuned
        { pitch_offset: -12, dur_mult: 0.5, amp: 0.25 },   # Low resonance
      ]
      
      srand(42)  # Reproducible "randomness"
      
      while time < duration
        # Cluster of notes (piano "gesture")
        cluster_size = rand(1..5)
        cluster_time = 0
        
        cluster_size.times do |i|
          base_pitch = 48 + rand(-12..24)
          prep = preparations.sample
          
          pitch = (base_pitch + prep[:pitch_offset]).round
          dur = (0.1 + rand * 0.5) * prep[:dur_mult]
          amp = prep[:amp] * (0.7 + rand * 0.3)
          
          events << play_note!(pitch, dur, amp)
          
          # Overlapping notes in cluster
          if i < cluster_size - 1 && rand > 0.5
            events << rest!(rand(0.02..0.1))
            cluster_time += rand(0.02..0.1)
          end
        end
        
        # Pause between gestures
        pause = rand(0.3..1.5)
        events << rest!(pause)
        time += cluster_time + pause + 0.3
      end
      
      sequence!(*events)
    end
    
    # WINDOWLICKER EQUATION: Spectrogram-derived melody
    # Using the spiral equation approach
    
    def self.equation_melody(base: 48, duration: 8.0)
      eq = PitchCategory::EquationMelody.new(
        PitchCategory::APHEX_EQUATIONS[:spiral],
        sample_rate: 8,
        quantize: :chromatic
      )
      
      pitches = eq.generate(duration)
      events = []
      
      pitches.each_with_index do |p, i|
        dur = 0.125 + (Math.sin(i * 0.3) * 0.05)
        amp = 0.2 + (Math.sin(i * 0.7) * 0.1)
        
        # Occasional chord instead of single note
        if rand < 0.15
          chord = [p, p + 4, p + 7].map { |n| (base + n - 60).clamp(24, 96) }
          events << play_chord!(chord, dur * 2, amp)
        else
          events << play_note!((base + p - 60).clamp(24, 96), dur, amp)
        end
      end
      
      sequence!(*events)
    end
    
    # POLYMETRIC CHAOS: Multiple time signatures simultaneously
    
    def self.polymetric_chaos(duration: 8.0)
      grid = RhythmCategory::PolymetricGrid.new(4, 5, 7,
        accents: [[0, 2], [0, 3], [0, 4, 6]])
      
      events = []
      
      grid.period.times do |t|
        break if t >= duration * 4  # Assume 4 subdivisions per beat
        
        alignment = grid.alignment_at(t)
        next if alignment.zero?
        
        # More aligned = louder, lower pitch
        pitch = 72 - alignment * 12
        amp = 0.15 + alignment * 0.12
        dur = 0.1 + alignment * 0.05
        
        events << play_note!(pitch, dur, amp)
        events << rest!(0.25 - dur) if dur < 0.25
      end
      
      sequence!(*events)
    end
  end
  
  # ============================================================================
  # PART VII: PATTERN BUILDERS - AUTECHRE
  # ============================================================================
  
  class AutechrePatterns
    extend FreeMonad::DSL
    
    # GENERATIVE RHYTHM: Markov chain over rhythmic cells
    # Key: Never quite repeating, but coherent
    
    def self.generative_rhythm(duration: 8.0, order: 2)
      # Define rhythmic cells (durations in 16th notes)
      cells = [
        [1],           # Single 16th
        [2],           # 8th note
        [3],           # Dotted 8th
        [1, 1],        # Two 16ths
        [1, 2],        # 16th + 8th
        [2, 1],        # 8th + 16th
        [1, 1, 1],     # Triplet-ish
        [4],           # Quarter
        [1, 1, 2],     # Syncopated
        [2, 2],        # Straight 8ths
      ]
      
      markov = MarkovSystems::HigherOrderMarkov.new(order, cells)
      
      # Train on a "seed" sequence
      seed = cells.sample(20)
      markov.train(seed)
      
      events = []
      time = 0
      beat_duration = 0.0625  # 16th note at 120bpm
      
      while time < duration
        cell = markov.step
        
        cell.each_with_index do |subdiv, i|
          dur = subdiv * beat_duration
          pitch = 48 + (i * 12) + rand(-2..2)  # Variation in pitch
          amp = 0.25 + rand * 0.15
          
          events << play_note!(pitch, dur, amp)
          time += dur
          
          break if time >= duration
        end
        
        # Occasional rest (Autechre's "breath")
        if rand < 0.15
          rest_dur = rand(1..3) * beat_duration
          events << rest!(rest_dur)
          time += rest_dur
        end
      end
      
      sequence!(*events)
    end
    
    # CELLULAR AUTOMATON EVOLUTION
    # Parameters evolve according to CA rules
    
    def self.cellular_rhythm(rule: 110, steps: 32)
      ca = CellularAutomata::ElementaryCA.new(16, rule: rule)
      
      events = []
      
      steps.times do |step|
        rhythm = ca.to_rhythm
        pitches = ca.to_pitches(base: 36, step: 2)
        
        # Play active cells
        rhythm.each_with_index do |active, i|
          if active == 1
            pitch = pitches.include?(36 + i * 2) ? 36 + i * 2 : 48
            dur = 0.05 + (step * 0.005)  # Gradually longer
            amp = 0.15 + (i * 0.02)
            
            events << play_note!(pitch, dur, amp)
          end
        end
        
        events << rest!(0.2)  # Gap between steps
        ca.step
      end
      
      sequence!(*events)
    end
    
    # SPECTRAL MORPH: Gradual timbral transformation
    # Autechre's approach: frequencies aren't notes, they're textures
    
    def self.spectral_morph(freq1: 100, freq2: 150, duration: 8.0, resolution: 32)
      events = []
      step_dur = duration / resolution
      
      resolution.times do |i|
        blend = i.to_f / (resolution - 1)
        
        # Get interpolated partials
        partials = PitchCategory.spectral_interpolation(freq1, freq2, blend, partials: 6)
        
        # Convert to MIDI (approximation)
        pitches = partials.map { |f| (69 + 12 * Math.log2(f / 440.0)).round }.uniq
        pitches = pitches.select { |p| p.between?(24, 96) }
        
        amp = 0.08 + (Math.sin(blend * Math::PI) * 0.05)  # Louder in middle
        
        events << play_chord!(pitches, step_dur * 1.5, amp)  # Overlap
        events << rest!(step_dur * 0.8) if i < resolution - 1
      end
      
      sequence!(*events)
    end
    
    # ANTI-GROOVE: Rhythms that resist quantization
    # Key: irrational timing, metric ambiguity
    
    def self.anti_groove(duration: 8.0)
      events = []
      time = 0
      
      base_pitches = [36, 41, 46, 48, 53]
      
      while time < duration
        # Use irrational ratios for duration
        ratio = RhythmCategory::IRRATIONAL_RATIOS.values.sample
        dur = 0.1 * ratio
        dur = dur.clamp(0.03, 0.5)
        
        pitch = base_pitches.sample
        
        # Pitch drift
        drift = PitchCategory::PitchDrift.new(pitch, max_deviation: 2, step_size: 0.3)
        actual_pitch = drift.next_pitch.round
        
        amp = 0.2 + rand * 0.2
        
        events << play_note!(actual_pitch, dur, amp)
        
        # Rest with irrational duration
        rest_ratio = RhythmCategory::IRRATIONAL_RATIOS.values.sample
        rest_dur = 0.05 * rest_ratio
        events << rest!(rest_dur) if rest_dur > 0.01
        
        time += dur + rest_dur
      end
      
      sequence!(*events)
    end
    
    # GAME OF LIFE TEXTURE
    # 2D CA for complex evolving texture
    
    def self.game_of_life_texture(generations: 16)
      gol = CellularAutomata::GameOfLife.new(8, 4, density: 0.4)
      
      events = []
      
      generations.times do |gen|
        pitches = gol.to_pitches(base: 36, x_step: 2, y_step: 12)
        
        if pitches.empty?
          # Extinction! Restart with new random state
          gol = CellularAutomata::GameOfLife.new(8, 4, density: 0.4)
          events << rest!(0.3)
        else
          # Play all living cells
          amp = 0.08 + (gol.population * 0.01)
          dur = 0.2 + (gen * 0.02)
          
          events << play_chord!(pitches.take(8), dur, amp.clamp(0, 0.4))
          events << rest!(0.15)
        end
        
        gol.step
      end
      
      sequence!(*events)
    end
    
    # QUANTUM RHYTHM: Superposition of multiple patterns
    # Only "collapses" on playback
    
    def self.quantum_rhythm(duration: 4.0)
      # Three rhythmic possibilities in superposition
      patterns = [
        -> { [0.25, 0.25, 0.5] },          # Straight
        -> { [0.33, 0.33, 0.34] },         # Triplet
        -> { [0.125, 0.375, 0.25, 0.25] }  # Syncopated
      ]
      
      superposition = QuantumPatterns::Superposition.new([
        [patterns[0], 0.4],
        [patterns[1], 0.35],
        [patterns[2], 0.25]
      ])
      
      events = []
      time = 0
      pitch = 48
      
      while time < duration
        # Measure/collapse the superposition
        pattern_fn = superposition.measure
        durations = pattern_fn.call
        
        durations.each do |dur|
          # Pitch follows its own logic
          pitch = ((pitch + rand(-5..5)) % 24) + 36
          amp = 0.2 + rand * 0.15
          
          events << play_note!(pitch, dur, amp)
          time += dur
          break if time >= duration
        end
      end
      
      sequence!(*events)
    end
  end
  
  # ============================================================================
  # PART VIII: SHOWCASE PATTERNS
  # ============================================================================
  
  class Showcase
    extend FreeMonad::DSL
    
    def self.aphex_showcase
      sequence!(
        section_marker("=== APHEX TWIN: DRILL 'N' BASS ==="),
        AphexTwinPatterns.drill_n_bass(duration: 4.0, intensity: 0.7),
        rest!(0.5),
        
        section_marker("=== APHEX TWIN: AMBIENT DRIFT ==="),
        AphexTwinPatterns.ambient_drift(base: 48, duration: 8.0),
        rest!(0.5),
        
        section_marker("=== APHEX TWIN: PREPARED PIANO ==="),
        AphexTwinPatterns.prepared_piano(duration: 6.0),
        rest!(0.5),
        
        section_marker("=== APHEX TWIN: EQUATION MELODY ==="),
        AphexTwinPatterns.equation_melody(base: 48, duration: 6.0),
        rest!(0.5),
        
        section_marker("=== APHEX TWIN: POLYMETRIC CHAOS ==="),
        AphexTwinPatterns.polymetric_chaos(duration: 6.0)
      )
    end
    
    def self.autechre_showcase
      sequence!(
        section_marker("=== AUTECHRE: GENERATIVE RHYTHM ==="),
        AutechrePatterns.generative_rhythm(duration: 6.0, order: 2),
        rest!(0.5),
        
        section_marker("=== AUTECHRE: CELLULAR AUTOMATON ==="),
        AutechrePatterns.cellular_rhythm(rule: 110, steps: 24),
        rest!(0.5),
        
        section_marker("=== AUTECHRE: SPECTRAL MORPH ==="),
        AutechrePatterns.spectral_morph(freq1: 100, freq2: 180, duration: 6.0),
        rest!(0.5),
        
        section_marker("=== AUTECHRE: ANTI-GROOVE ==="),
        AutechrePatterns.anti_groove(duration: 5.0),
        rest!(0.5),
        
        section_marker("=== AUTECHRE: GAME OF LIFE ==="),
        AutechrePatterns.game_of_life_texture(generations: 20),
        rest!(0.5),
        
        section_marker("=== AUTECHRE: QUANTUM RHYTHM ==="),
        AutechrePatterns.quantum_rhythm(duration: 4.0)
      )
    end
    
    def self.quantum_electronic_showcase
      sequence!(
        section_marker("╔══════════════════════════════════════╗"),
        section_marker("║  QUANTUM ELECTRONIC MUSIC SHOWCASE   ║"),
        section_marker("║  Aphex Twin × Autechre × Category    ║"),
        section_marker("╚══════════════════════════════════════╝"),
        rest!(0.5),
        
        aphex_showcase,
        rest!(1.0),
        
        autechre_showcase,
        rest!(1.0),
        
        section_marker("=== FINALE: COLLISION ==="),
        # Both styles simultaneously
        parallel!(
          AphexTwinPatterns.drill_n_bass(duration: 4.0, intensity: 0.5),
          AutechrePatterns.anti_groove(duration: 4.0)
        )
      )
    end
    
    private
    
    def self.section_marker(name)
      FreeMonad::Pure.new(name)
    end
  end
end
