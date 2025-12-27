# lib/seed_miner_42d.rb
#
# Seed Mining around 0x42D for Musical Leitmotifs
#
# 0x42D = 1069 decimal
# In ASCII: "B-" (incomplete, suggestive)
#
# This module pre-mines seeds in the neighborhood of 0x42D
# to find those most conducive to:
# 1. Harmonic leitmotifs
# 2. Girard-compatible color progressions
# 3. Interval structures that maximize consonance while maintaining interest

require_relative 'girard_colors'

module SeedMiner42D
  BASE_SEED = 0x42D  # 1069
  
  # Special seeds discovered through mining
  KNOWN_GOOD_SEEDS = {
    0x42D => {
      name: "The Cleft",
      description: "Base seed - balanced polarity",
      character: :neutral
    },
    0x42E => {
      name: "One Step Beyond",
      description: "Slight positive shift",
      character: :ascending
    },
    0x42C => {
      name: "One Step Back",
      description: "Slight negative shift", 
      character: :descending
    }
  }.freeze

  # Pre-mine the neighborhood
  def self.premine(radius: 500, chain_length: 12)
    puts "Mining seeds around 0x42D (radius: #{radius})..."
    
    results = SeedMiner.mine(BASE_SEED, radius: radius, chain_length: chain_length, top_n: 20)
    
    puts "\nTop 10 seeds by musical quality:"
    puts "=" * 70
    
    results.first(10).each_with_index do |r, i|
      puts "#{i + 1}. #{r[:seed_hex]}"
      puts "   Total: #{r[:total_score].round(3)} | " \
           "Intervals: #{r[:interval_variety].round(2)} | " \
           "Consonance: #{r[:consonance].round(2)} | " \
           "Leitmotif: #{r[:leitmotif_score].round(2)}"
    end
    
    results
  end

  # Pre-mine with Girard constraints
  def self.premine_girard(radius: 500, chain_length: 12)
    puts "Mining Girard-compatible seeds around 0x42D..."
    
    results = SeedMiner.mine_girard(BASE_SEED, radius: radius, chain_length: chain_length)
    
    puts "\nTop Girard-compatible seeds:"
    puts "=" * 70
    
    results.each_with_index do |r, i|
      polarities = r[:girard_polarities].map { |p| p.to_s[0].upcase }.join
      connectives = r[:girard_connectives].map { |c| girard_symbol(c) }.join
      
      puts "#{i + 1}. #{r[:seed_hex]}"
      puts "   Polarities:   #{polarities}"
      puts "   Connectives:  #{connectives}"
      puts "   Balance: #{r[:polarity_balance].round(2)} | Score: #{r[:total_score].round(3)}"
    end
    
    results
  end

  # Generate leitmotif from 0x42D
  def self.leitmotif(length: 8, base_pitch: 60)
    LeitmotifGenerator.from_seed(BASE_SEED, length: length, base_pitch: base_pitch)
  end

  # Generate interval-specified leitmotif
  # Classic intervals for leitmotifs:
  # - Wagner Tristan: [0, -1, +2] (longing)
  # - Ring: [4, -4, 7] (heroic)
  # - Fate: [-3, -2, -1] (descending)
  def self.leitmotif_from_intervals(name, intervals, base_pitch: 60)
    leit = LeitmotifGenerator.from_intervals(intervals, start_pitch: base_pitch, seed: BASE_SEED)
    leit[:name] = name
    leit
  end

  # Pre-defined leitmotif patterns
  LEITMOTIF_PATTERNS = {
    # Named after Girard's logical concepts
    cleft: [0, 7, -5, 4],           # The split: up fifth, down fourth, up third
    tensor: [4, 3, 5],               # ⊗: Major triad arpeggiation
    par: [-4, -3, -5],               # ⅋: Inverse of tensor
    bang: [12, 0, 0],                # !: Octave leap, then stasis
    quest: [1, -1, 1, -1],           # ?: Chromatic oscillation (uncertainty)
    cut: [6, -6, 0],                 # Tritone tension, resolution to unison
    axiom: [7, 5, -12],              # Perfect motion: fifth up, fourth up, octave down
    
    # Musical archetypes
    ascending: [2, 2, 1, 2],         # Major scale fragment
    descending: [-2, -2, -1, -2],    # Descending major
    chromatic_rise: [1, 1, 1, 1],    # Tension building
    chromatic_fall: [-1, -1, -1, -1], # Tension releasing
    heroic: [4, 3, 5, -5],           # Major arpeggio + resolution
    tragic: [-3, -4, -5, 7],         # Minor descent + leap
  }.freeze

  # Generate all pattern leitmotifs
  def self.all_patterns(base_pitch: 60)
    LEITMOTIF_PATTERNS.map do |name, intervals|
      leitmotif_from_intervals(name, intervals, base_pitch: base_pitch)
    end
  end

  # Find seeds that produce specific interval patterns
  def self.find_seeds_for_pattern(pattern, radius: 1000, tolerance: 1)
    matching = []
    
    (BASE_SEED - radius..BASE_SEED + radius).each do |seed|
      leit = LeitmotifGenerator.from_seed(seed, length: pattern.size + 1)
      
      if intervals_match?(leit[:intervals], pattern, tolerance: tolerance)
        matching << {
          seed: seed,
          seed_hex: "0x#{seed.to_s(16).upcase}",
          intervals: leit[:intervals],
          match_quality: interval_match_quality(leit[:intervals], pattern)
        }
      end
    end
    
    matching.sort_by { |m| -m[:match_quality] }
  end

  # Harmonize leitmotif with Girard colors
  def self.harmonize_with_girard(leitmotif)
    notes = leitmotif[:notes]
    
    harmonized = notes.map.with_index do |note, i|
      polarity = note[:girard_polarity]
      
      # Add harmony based on polarity
      harmony = case polarity
                when :positive then [note[:pitch] + 4, note[:pitch] + 7]  # Major
                when :negative then [note[:pitch] + 3, note[:pitch] + 7]  # Minor
                when :additive then [note[:pitch] + 4, note[:pitch] + 8]  # Augmented
                when :multiplicative then [note[:pitch] + 3, note[:pitch] + 6]  # Diminished
                else [note[:pitch] + 5, note[:pitch] + 7]  # Sus4
                end
      
      note.merge(
        harmony: harmony,
        chord_type: polarity,
        girard_color: GirardColors::PALETTE[polarity_to_color(polarity)]
      )
    end
    
    leitmotif.merge(harmonized_notes: harmonized)
  end

  # Render to OSC messages
  def self.to_osc(leitmotif, synth: "sine")
    messages = []
    time = 0.0
    
    notes = leitmotif[:harmonized_notes] || leitmotif[:notes]
    
    notes.each_with_index do |note, i|
      # Main note
      messages << {
        time: time,
        address: "/s_new",
        args: [synth, -1, 1, 0,
               "freq", midi_to_freq(note[:pitch]),
               "amp", note[:velocity] / 127.0,
               "sustain", note[:duration]]
      }
      
      # Harmony notes if present
      if note[:harmony]
        note[:harmony].each do |h_pitch|
          messages << {
            time: time,
            address: "/s_new",
            args: [synth, -1, 1, 0,
                   "freq", midi_to_freq(h_pitch),
                   "amp", (note[:velocity] / 127.0) * 0.6,
                   "sustain", note[:duration]]
          }
        end
      end
      
      time += note[:duration]
    end
    
    messages
  end

  private

  def self.girard_symbol(connective)
    case connective
    when :tensor then "⊗"
    when :par    then "⅋"
    when :plus   then "⊕"
    when :with   then "&"
    when :bang   then "!"
    else "·"
    end
  end

  def self.intervals_match?(actual, target, tolerance: 0)
    return false if actual.size != target.size
    
    actual.zip(target).all? { |a, t| (a - t).abs <= tolerance }
  end

  def self.interval_match_quality(actual, target)
    return 0 if actual.size != target.size
    
    diffs = actual.zip(target).map { |a, t| (a - t).abs }
    1.0 / (1 + diffs.sum)
  end

  def self.polarity_to_color(polarity)
    case polarity
    when :positive then :positive
    when :negative then :negative
    when :additive then :plus
    when :multiplicative then :tensor
    else :axiom
    end
  end

  def self.midi_to_freq(midi)
    440.0 * (2.0 ** ((midi - 69) / 12.0))
  end
end

# Interactive mining script when run directly
if __FILE__ == $0
  puts "=" * 70
  puts "🎵 SEED MINER 0x42D: Girard-Harmonized Leitmotif Generator"
  puts "=" * 70
  puts ""
  
  # Pre-mine
  puts "Phase 1: Mining neighborhood..."
  top_seeds = SeedMiner42D.premine(radius: 200)
  
  puts "\nPhase 2: Girard compatibility check..."
  girard_seeds = SeedMiner42D.premine_girard(radius: 200)
  
  puts "\nPhase 3: Generating leitmotifs from 0x42D..."
  base_leit = SeedMiner42D.leitmotif
  puts "Base leitmotif intervals: #{base_leit[:intervals]}"
  puts "Polarities: #{base_leit[:polarities]}"
  
  puts "\nPhase 4: Pattern leitmotifs..."
  SeedMiner42D::LEITMOTIF_PATTERNS.each do |name, intervals|
    puts "  #{name}: #{intervals}"
  end
  
  puts "\nPhase 5: Harmonized output..."
  harmonized = SeedMiner42D.harmonize_with_girard(base_leit)
  harmonized[:harmonized_notes].each_with_index do |note, i|
    puts "  Note #{i}: pitch=#{note[:pitch]}, chord=#{note[:chord_type]}, harmony=#{note[:harmony]}"
  end
  
  puts "\n✓ Mining complete. Best seed: #{top_seeds.first[:seed_hex]}"
end
