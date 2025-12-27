# lib/girard_colors.rb
#
# Girard's "Cleft de Logique" (Key of Logic) Color System
#
# In linear logic and proof nets, Girard uses color to distinguish:
# - Polarity: Positive (⊕, ⊗) vs Negative (⅋, &)
# - Multiplicative vs Additive connectives
# - Cut elimination phases
# - The geometry of interaction
#
# Musical mapping:
# - Positive polarity → Major mode, tension, forward motion
# - Negative polarity → Minor mode, resolution, backward motion
# - Multiplicative → Parallel voice motion
# - Additive → Contrary motion
# - Cut elimination → Dissonance resolution

module GirardColors
  # Girard's logical color palette
  # Based on his proof net visualizations
  PALETTE = {
    # Polarity colors
    positive: { hue: 0,   name: "red",    musical: :major },
    negative: { hue: 240, name: "blue",   musical: :minor },
    
    # Connective colors
    tensor:   { hue: 30,  name: "orange", musical: :parallel_fifth },
    par:      { hue: 270, name: "violet", musical: :contrary_motion },
    plus:     { hue: 120, name: "green",  musical: :additive },
    with:     { hue: 180, name: "cyan",   musical: :shared_tone },
    
    # Dynamics colors
    cut:      { hue: 60,  name: "yellow", musical: :dissonance },
    axiom:    { hue: 300, name: "magenta", musical: :consonance },
    
    # The cleft itself
    cleft:    { hue: 0,   name: "white",  musical: :cadence }
  }.freeze

  # Linear logic connective to musical interval
  CONNECTIVE_INTERVALS = {
    tensor: 7,   # ⊗ = perfect fifth (parallel structure)
    par:    5,   # ⅋ = perfect fourth (inverse of fifth)
    plus:   4,   # ⊕ = major third (additive, bright)
    with:   3,   # & = minor third (shared, dark)
    bang:   12,  # ! = octave (exponential = identity)
    quest:  0,   # ? = unison (why-not = no motion)
  }.freeze

  # Polarity to musical mode
  def self.polarity_to_mode(polarity)
    case polarity
    when :positive then :major
    when :negative then :minor
    when :neutral  then :dorian  # balanced
    end
  end

  # Convert Girard color to LCH
  def self.to_lch(color_name, lightness: 65, chroma: 50)
    color = PALETTE[color_name.to_sym]
    return nil unless color
    { L: lightness, C: chroma, H: color[:hue] }
  end

  # Proof net edge to musical interval
  def self.edge_to_interval(from_polarity, to_polarity, connective)
    base = CONNECTIVE_INTERVALS[connective] || 0
    
    # Polarity shift adds tension
    if from_polarity != to_polarity
      base += 1  # Add semitone tension
    end
    
    base % 12
  end

  # Cut elimination = dissonance resolution
  class CutElimination
    attr_reader :steps, :resolved

    def initialize
      @steps = []
      @resolved = false
    end

    def add_dissonance(interval)
      @steps << { type: :dissonance, interval: interval, color: :cut }
    end

    def resolve(target_interval)
      @steps << { type: :resolution, interval: target_interval, color: :axiom }
      @resolved = target_interval.zero? || [0, 7, 12].include?(target_interval)
    end

    def to_progression
      @steps.map { |s| s[:interval] }
    end
  end

  # Geometry of Interaction → Voice leading
  class GeometryOfInteraction
    attr_reader :tokens, :traces

    def initialize
      @tokens = []  # Active "particles" in the proof net
      @traces = []  # Paths taken
    end

    def emit(pitch, polarity)
      @tokens << { pitch: pitch, polarity: polarity, active: true }
    end

    def interact(token1_idx, token2_idx)
      t1 = @tokens[token1_idx]
      t2 = @tokens[token2_idx]
      
      return nil unless t1 && t2 && t1[:active] && t2[:active]
      
      # Opposite polarities annihilate (resolve)
      if t1[:polarity] != t2[:polarity]
        interval = (t1[:pitch] - t2[:pitch]).abs % 12
        @traces << { from: t1[:pitch], to: t2[:pitch], interval: interval }
        t1[:active] = false
        t2[:active] = false
        return { type: :annihilation, interval: interval }
      end
      
      # Same polarity = parallel motion
      { type: :parallel, pitches: [t1[:pitch], t2[:pitch]] }
    end

    def trace_to_melody
      @traces.flat_map { |t| [t[:from], t[:to]] }.uniq
    end
  end
end

# Seed Mining for Musical Quality
module SeedMiner
  # Golden ratio for maximally irrational angle
  PHI = (1 + Math.sqrt(5)) / 2
  GOLDEN_ANGLE = 360.0 / (PHI ** 2)  # ≈ 137.508°

  # SplitMix64 (same as Gay.jl)
  class SplitMix64
    def initialize(seed)
      @state = seed & 0xFFFFFFFFFFFFFFFF
    end

    def next_u64
      @state = (@state + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
      z = @state
      z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
      z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
      z ^ (z >> 31)
    end

    def next_float
      next_u64.to_f / 0xFFFFFFFFFFFFFFFF.to_f
    end
  end

  # Generate color from seed at index (matches Gay.jl algorithm)
  def self.color_at(seed, index)
    rng = SplitMix64.new(seed)
    index.times { rng.next_u64 }  # Advance to position
    
    # LCH generation
    l = 10 + rng.next_float * 85  # L: 10-95
    c = rng.next_float * 100       # C: 0-100
    h = rng.next_float * 360       # H: 0-360
    
    { L: l, C: c, H: h, index: index }
  end
  
  # Convert LCH to hex (simplified perceptual approximation)
  def self.lch_to_hex(l, c, h)
    h_rad = h * Math::PI / 180
    a = c * Math.cos(h_rad) * 0.01
    b = c * Math.sin(h_rad) * 0.01
    l_norm = l / 100.0
    
    r = [[l_norm + a, 0].max, 1].min
    g = [[l_norm - 0.5 * a.abs - 0.5 * b.abs, 0].max, 1].min
    bl = [[l_norm + b, 0].max, 1].min
    
    "#%02X%02X%02X" % [(r * 255).round, (g * 255).round, (bl * 255).round]
  end

  # Evaluate seed's musical quality
  def self.evaluate_seed(seed, chain_length: 12)
    colors = (0...chain_length).map { |i| color_at(seed, i) }
    
    # Extract hues as pitch classes
    pitches = colors.map { |c| (c[:H] / 30.0).round % 12 }
    
    # Evaluate metrics
    {
      seed: seed,
      seed_hex: "0x#{seed.to_s(16).upcase}",
      
      # Interval variety (entropy)
      interval_variety: interval_variety(pitches),
      
      # Consonance score (perfect intervals)
      consonance: consonance_score(pitches),
      
      # Girard polarity balance
      polarity_balance: polarity_balance(colors),
      
      # Leitmotif potential (recurring patterns)
      leitmotif_score: leitmotif_potential(pitches),
      
      # Circle of fifths alignment
      cof_alignment: circle_of_fifths_alignment(pitches),
      
      # Combined score
      total_score: nil  # Computed below
    }.tap do |result|
      result[:total_score] = (
        result[:interval_variety] * 0.2 +
        result[:consonance] * 0.25 +
        result[:polarity_balance] * 0.15 +
        result[:leitmotif_score] * 0.25 +
        result[:cof_alignment] * 0.15
      )
    end
  end

  # Mine seeds around a base, return best
  def self.mine(base_seed, radius: 1000, chain_length: 12, top_n: 10)
    candidates = (-radius..radius).map do |offset|
      seed = (base_seed + offset) & 0xFFFFFFFFFFFFFFFF
      evaluate_seed(seed, chain_length: chain_length)
    end
    
    candidates.sort_by { |c| -c[:total_score] }.first(top_n)
  end

  # Pre-mine with Girard color constraints
  def self.mine_girard(base_seed, radius: 1000, chain_length: 12)
    candidates = mine(base_seed, radius: radius, chain_length: chain_length, top_n: 100)
    
    # Filter for Girard-compatible (polarity balance > 0.4)
    girard_compatible = candidates.select { |c| c[:polarity_balance] > 0.4 }
    
    # Annotate with Girard analysis
    girard_compatible.first(10).map do |c|
      colors = (0...chain_length).map { |i| color_at(c[:seed], i) }
      c.merge(
        girard_polarities: colors.map { |col| hue_to_polarity(col[:H]) },
        girard_connectives: derive_connectives(colors)
      )
    end
  end

  private

  def self.interval_variety(pitches)
    intervals = pitches.each_cons(2).map { |a, b| (b - a) % 12 }
    unique = intervals.uniq.size
    unique.to_f / [intervals.size, 1].max
  end

  def self.consonance_score(pitches)
    intervals = pitches.each_cons(2).map { |a, b| (b - a) % 12 }
    consonant = [0, 3, 4, 5, 7, 8, 9, 12]  # P1, m3, M3, P4, P5, m6, M6, P8
    count = intervals.count { |i| consonant.include?(i) }
    count.to_f / [intervals.size, 1].max
  end

  def self.polarity_balance(colors)
    # Hue 0-180 = positive, 180-360 = negative
    positive = colors.count { |c| c[:H] < 180 }
    negative = colors.size - positive
    1.0 - (positive - negative).abs.to_f / colors.size
  end

  def self.leitmotif_potential(pitches)
    # Look for recurring 2-3 note patterns
    bigrams = pitches.each_cons(2).map { |a, b| [a, b] }
    trigrams = pitches.each_cons(3).map { |a, b, c| [a, b, c] }
    
    bigram_repeats = bigrams.group_by(&:itself).values.count { |v| v.size > 1 }
    trigram_repeats = trigrams.group_by(&:itself).values.count { |v| v.size > 1 }
    
    (bigram_repeats * 0.3 + trigram_repeats * 0.7) / [pitches.size / 3.0, 1].max
  end

  def self.circle_of_fifths_alignment(pitches)
    # Score based on fifths relationships
    intervals = pitches.each_cons(2).map { |a, b| (b - a) % 12 }
    fifths = intervals.count { |i| [5, 7].include?(i) }  # P4 or P5
    fifths.to_f / [intervals.size, 1].max
  end

  def self.hue_to_polarity(hue)
    case hue
    when 0...60    then :positive    # Red-orange
    when 60...120  then :additive    # Yellow-green
    when 120...180 then :neutral     # Green-cyan
    when 180...240 then :negative    # Cyan-blue
    when 240...300 then :multiplicative  # Blue-magenta
    else :positive  # Magenta-red
    end
  end

  def self.derive_connectives(colors)
    colors.each_cons(2).map do |c1, c2|
      hue_diff = (c2[:H] - c1[:H]).abs
      case hue_diff
      when 0...30   then :bang      # !: minimal change
      when 30...90  then :tensor    # ⊗: parallel
      when 90...150 then :plus      # ⊕: additive
      when 150...210 then :par      # ⅋: contrary
      else :with    # &: shared
      end
    end
  end
end

# Leitmotif Generator from Seeds
module LeitmotifGenerator
  # Generate leitmotif from seed
  def self.from_seed(seed, length: 8, base_pitch: 60)
    colors = (0...length).map { |i| SeedMiner.color_at(seed, i) }
    
    # Map colors to pitches and durations
    notes = colors.map.with_index do |color, i|
      pitch = base_pitch + ((color[:H] / 30.0).round % 12)
      duration = 0.25 + (color[:L] / 100.0) * 0.5  # 0.25-0.75
      velocity = 40 + (color[:C] * 0.6).round      # 40-100
      
      {
        pitch: pitch,
        duration: duration,
        velocity: velocity,
        color: color,
        girard_polarity: SeedMiner.send(:hue_to_polarity, color[:H])
      }
    end
    
    {
      seed: seed,
      seed_hex: "0x#{seed.to_s(16).upcase}",
      notes: notes,
      intervals: notes.each_cons(2).map { |a, b| b[:pitch] - a[:pitch] },
      polarities: notes.map { |n| n[:girard_polarity] }
    }
  end

  # Generate motif (shorter, 3-4 notes)
  def self.motif(seed, start_index: 0, length: 4)
    from_seed(seed, length: length).tap do |m|
      m[:type] = :motif
      m[:start_index] = start_index
    end
  end

  # Generate full leitmotif with variations
  def self.with_variations(seed, variation_count: 3)
    base = from_seed(seed)
    
    variations = (1..variation_count).map do |v|
      # Vary by shifting seed slightly
      varied_seed = seed + v * 7  # Prime offset
      varied = from_seed(varied_seed)
      varied[:variation] = v
      varied[:relationship] = :transposition if intervals_match?(base, varied)
      varied
    end
    
    {
      base: base,
      variations: variations,
      girard_structure: analyze_girard_structure(base, variations)
    }
  end

  # Create interval-specified leitmotif
  def self.from_intervals(intervals, start_pitch: 60, seed: 0x42D)
    colors = (0..intervals.size).map { |i| SeedMiner.color_at(seed, i) }
    
    pitches = [start_pitch]
    intervals.each { |i| pitches << pitches.last + i }
    
    notes = pitches.zip(colors).map do |pitch, color|
      {
        pitch: pitch,
        duration: 0.5,
        velocity: 80,
        color: color,
        girard_polarity: SeedMiner.send(:hue_to_polarity, color[:H])
      }
    end
    
    {
      seed: seed,
      intervals: intervals,
      notes: notes,
      type: :interval_specified
    }
  end

  private

  def self.intervals_match?(leit1, leit2)
    leit1[:intervals] == leit2[:intervals]
  end

  def self.analyze_girard_structure(base, variations)
    # Count polarity transitions
    base_polarities = base[:polarities]
    transitions = base_polarities.each_cons(2).count { |a, b| a != b }
    
    {
      polarity_transitions: transitions,
      dominant_polarity: base_polarities.group_by(&:itself)
                                        .max_by { |_, v| v.size }&.first,
      cut_points: find_cut_points(base[:notes]),
      resolution_points: find_resolution_points(base[:notes])
    }
  end

  def self.find_cut_points(notes)
    # Dissonant intervals = cut points
    notes.each_cons(2).each_with_index.select do |(n1, n2), i|
      interval = (n2[:pitch] - n1[:pitch]).abs % 12
      [1, 2, 6, 10, 11].include?(interval)  # Dissonant
    end.map { |_, i| i }
  end

  def self.find_resolution_points(notes)
    # Consonant intervals after dissonance = resolution
    notes.each_cons(2).each_with_index.select do |(n1, n2), i|
      interval = (n2[:pitch] - n1[:pitch]).abs % 12
      [0, 5, 7, 12].include?(interval)  # P1, P4, P5, P8
    end.map { |_, i| i }
  end
end
