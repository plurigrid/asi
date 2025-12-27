# lib/tritwise_letter_spirit.rb
#
# 3-Agent Color Matching with p-adic Grounding
# Hofstadter Letter Spirit: strange loops of perception-action
#
# Key invariants (verified in lean4/):
#   - Spectral gap = 1/4, mixing time = 4 steps
#   - μ(3) = -1 for Möbius inversion
#   - 3-MATCH at depth d ⟺ v₃(c₁-c₂) ≥ d
#
# Each entropy event triggers:
#   1. 3-MATCH attempt (do colors align at current depth?)
#   2. Möbius inversion (generate next color)
#   3. Strange loop (feed output back as perception)

require_relative 'moebius'
require_relative 'girard_colors'
require_relative 'blume_capel_coinflip'
require 'securerandom'

module TritwiseLetterSpirit
  # Verified constants (see lean4/MusicTopos/Basic.lean)
  SPECTRAL_GAP = Rational(1, 4)
  MIXING_TIME = 4
  GOLDEN_ANGLE = 137.508  # degrees
  
  # p = 3 for ternary system
  P = 3
  
  # 3-adic valuation: v₃(n) = max{k : 3^k | n}
  def self.padic_valuation(n, p = P)
    return Float::INFINITY if n.zero?
    v = 0
    n = n.abs
    while (n % p).zero?
      v += 1
      n /= p
    end
    v
  end
  
  # 3-adic norm: |n|₃ = 3^(-v₃(n))
  def self.padic_norm(n, p = P)
    v = padic_valuation(n, p)
    return 0.0 if v == Float::INFINITY
    p ** (-v)
  end
  
  # Colors match at depth d iff v₃(c₁ - c₂) ≥ d
  def self.colors_match_at_depth?(c1, c2, depth)
    diff = (c1 - c2).abs
    padic_valuation(diff) >= depth
  end
  
  # ═══════════════════════════════════════════════════════════════
  # AGENT: Identity + State + Perception
  # ═══════════════════════════════════════════════════════════════
  
  class Agent
    attr_accessor :identity, :state, :perception, :color
    
    def initialize(seed)
      @identity = seed        # Immutable
      @state = 0              # Mutable index
      @perception = 0         # Current perceived hue (mod 360)
      @color = nil            # Full color data
      advance!
    end
    
    def advance!
      @state += 1
      @color = SeedMiner.color_at(@identity, @state)
      @perception = @color[:H].to_i
      self
    end
    
    def to_h
      { identity: @identity, state: @state, perception: @perception, color: @color }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # LETTER SPIRIT SYSTEM: 3 Agents in Strange Loop
  # ═══════════════════════════════════════════════════════════════
  
  class LetterSpiritSystem
    attr_reader :agents, :epoch, :match_depth, :history
    
    def initialize(seeds)
      raise ArgumentError, "Need exactly 3 seeds" unless seeds.size == 3
      @agents = seeds.map { |s| Agent.new(s) }
      @epoch = 0
      @match_depth = 0
      @history = []
    end
    
    # Get all 3 perceptions
    def perceptions
      @agents.map(&:perception)
    end
    
    # Pairwise differences for 3-MATCH
    def pairwise_diffs
      p = perceptions
      [p[0] - p[1], p[1] - p[2], p[2] - p[0]]
    end
    
    # Check if we have a 3-MATCH at current depth
    def three_match?
      pairwise_diffs.all? do |diff|
        TritwiseLetterSpirit.padic_valuation(diff.abs) >= @match_depth
      end
    end
    
    # Generate next color via Möbius inversion: μ(3) = -1
    def interaction_color
      sum = perceptions.sum
      moebius_weight = Moebius.mu(3)  # -1
      (sum * moebius_weight).abs % 360
    end
    
    # ═════════════════════════════════════════════════════════════
    # ENTROPY EVENT: Trigger 3-MATCH attempt
    # ═════════════════════════════════════════════════════════════
    
    def process_entropy!(source: "local", bits: nil)
      bits ||= SecureRandom.random_number(2**64)
      trit = (bits % 3) - 1  # -1, 0, or +1
      
      # 1. Attempt 3-MATCH
      matched = three_match?
      @match_depth += 1 if matched
      
      # 2. Compute next color via Möbius inversion
      next_perception = interaction_color
      
      # 3. Strange loop: blend with trit perturbation
      @agents.each_with_index do |agent, i|
        agent.advance!
        # Perception influenced by group + individual perturbation
        blend = (next_perception + (trit * (i + 1))) % 360
        agent.perception = (agent.perception + blend) / 2
      end
      
      @epoch += 1
      
      # Record history
      event = {
        epoch: @epoch,
        source: source,
        trit: trit,
        perceptions: perceptions.dup,
        diffs: pairwise_diffs,
        valuations: pairwise_diffs.map { |d| TritwiseLetterSpirit.padic_valuation(d.abs) },
        matched: matched,
        match_depth: @match_depth,
        next_perception: next_perception,
        girard_polarities: @agents.map { |a| SeedMiner.send(:hue_to_polarity, a.color[:H]) }
      }
      @history << event
      event
    end
    
    # Run until mixed (spectral gap convergence)
    def run_until_mixed!
      MIXING_TIME.times { process_entropy! }
      { mixed: true, epoch: @epoch, match_depth: @match_depth }
    end
    
    # Hofstadter strange loop: extended interaction
    def strange_loop!(iterations = 12)
      iterations.times do |i|
        event = process_entropy!(source: "strange_loop_#{i}")
        
        # Feed output back: one agent gets its seed updated
        rotating_agent = @agents[i % 3]
        # The "letter" learned becomes part of the "spirit"
        rotating_agent.instance_variable_set(:@identity, 
          (rotating_agent.identity + event[:next_perception]) % (2**32))
      end
      @history
    end
    
    # ═════════════════════════════════════════════════════════════
    # ABELIAN EXTENSION: Split into 3 subsystems
    # ═════════════════════════════════════════════════════════════
    
    def split!
      base = interaction_color
      
      # Each agent becomes center of new tritwise system
      @agents.map do |center_agent|
        seeds = [
          center_agent.identity,
          (center_agent.identity + base) % (2**32),
          (center_agent.identity + base * 2) % (2**32)
        ]
        LetterSpiritSystem.new(seeds)
      end
    end
    
    # ═════════════════════════════════════════════════════════════
    # AUDIO INTEGRATION: Map to Overtone/OSC
    # ═════════════════════════════════════════════════════════════
    
    def to_osc_events
      @history.map do |event|
        # Map perceptions to frequencies
        freqs = event[:perceptions].map { |h| 220.0 * (2 ** (h / 360.0)) }
        
        # Map match depth to amplitude
        amp = 0.2 + (event[:match_depth] * 0.1)
        amp = [amp, 0.8].min
        
        # Map trit to pan
        pan = event[:trit] * 0.5  # -0.5, 0, or +0.5
        
        {
          epoch: event[:epoch],
          freqs: freqs,
          amp: amp,
          pan: pan,
          matched: event[:matched],
          polarities: event[:girard_polarities]
        }
      end
    end
    
    def to_s
      "LetterSpirit(epoch=#{@epoch}, depth=#{@match_depth}, perceptions=#{perceptions})"
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # DEMO / SHOWCASE
  # ═══════════════════════════════════════════════════════════════
  
  def self.demo(seeds = [0x42D, 0x69, 0x137])
    puts "╔═══════════════════════════════════════════════════════════════╗"
    puts "║  Tritwise Letter Spirit: 3-Agent Color Matching              ║"
    puts "╚═══════════════════════════════════════════════════════════════╝"
    puts
    puts "Seeds: #{seeds.map { |s| "0x#{s.to_s(16).upcase}" }.join(', ')}"
    puts "Spectral Gap: #{SPECTRAL_GAP} → Mixing Time: #{MIXING_TIME} steps"
    puts
    
    system = LetterSpiritSystem.new(seeds)
    
    puts "Running strange loop for 12 iterations..."
    puts
    
    system.strange_loop!(12).each do |event|
      match_indicator = event[:matched] ? "✓ 3-MATCH" : "○ seeking"
      polarities = event[:girard_polarities].map { |p| p.to_s[0].upcase }.join
      
      puts "Epoch #{event[:epoch].to_s.rjust(2)}: " \
           "perceptions=#{event[:perceptions].inspect.ljust(20)} " \
           "v₃=#{event[:valuations].inspect.ljust(12)} " \
           "depth=#{event[:match_depth]} " \
           "#{match_indicator} " \
           "[#{polarities}]"
    end
    
    puts
    puts "Final state: #{system}"
    puts
    puts "Splitting into 3 subsystems..."
    subsystems = system.split!
    subsystems.each_with_index do |sub, i|
      puts "  Subsystem #{i + 1}: seeds=#{sub.agents.map(&:identity).map { |s| "0x#{(s % 0x10000).to_s(16)}" }}"
    end
    
    system
  end
end

# Run demo if executed directly
if __FILE__ == $0
  TritwiseLetterSpirit.demo
end
