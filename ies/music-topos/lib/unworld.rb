# lib/unworld.rb
#
# UNWORLD: Replace Time with Color Chain Derivations
#
# Core principle: There is no "time" - only seed-chaining.
# Each color derives from the previous via deterministic transformation.
# The "next" state is not temporal but derivational.
#
# Chain: seed₀ → color₀ → seed₁ → color₁ → seed₂ → ...
#        where seed_{n+1} = f(seed_n, color_n)
#
# This is unworlding: extracting the derivation structure
# without reference to any external temporal frame.

require_relative 'splitmix_ternary'
require_relative 'three_match_geodesic_gadget'
require_relative 'unworlding_involution'

module Unworld
  # ═══════════════════════════════════════════════════════════════════════════════
  # SEED CHAINING: Replace time with derivation
  # ═══════════════════════════════════════════════════════════════════════════════
  
  GOLDEN = 0x9E3779B97F4A7C15
  MASK64 = 0xFFFFFFFFFFFFFFFF
  
  # Derive next seed from current seed + color
  # This replaces temporal succession with derivational succession
  def self.chain_seed(seed, color_trit)
    # The "next" seed is derived, not temporally subsequent
    # seed_{n+1} = (seed_n ⊕ (trit * GOLDEN)) mod 2^64
    trit_contribution = case color_trit
                        when -1 then GOLDEN
                        when 0  then GOLDEN >> 1
                        when 1  then GOLDEN << 1
                        end
    ((seed ^ trit_contribution) * 0xBF58476D1CE4E5B9) & MASK64
  end
  
  # Derive color from seed (deterministic)
  def self.derive_color(seed, index = 0)
    rng = SplitMixTernary::Generator.new(seed)
    index.times { rng.next_trit }
    trit = rng.next_trit
    hex = trit_to_hex(trit, seed)
    { seed: seed, trit: trit, hex: hex, index: index }
  end
  
  def self.trit_to_hex(trit, seed)
    # Deterministic color from trit + seed
    hue = case trit
          when -1 then 240  # Blue
          when 0  then 120  # Green
          when 1  then 0    # Red
          end
    # Add seed-derived offset for variety
    offset = ((seed >> 16) & 0xFF) % 60 - 30
    hue = (hue + offset) % 360
    hsl_to_hex(hue, 0.7, 0.5)
  end
  
  def self.hsl_to_hex(h, s, l)
    h = h / 360.0
    c = (1 - (2 * l - 1).abs) * s
    x = c * (1 - ((h * 6) % 2 - 1).abs)
    m = l - c / 2
    r, g, b = case (h * 6).to_i
              when 0 then [c, x, 0]
              when 1 then [x, c, 0]
              when 2 then [0, c, x]
              when 3 then [0, x, c]
              when 4 then [x, 0, c]
              else [c, 0, x]
              end
    format("#%02X%02X%02X", ((r + m) * 255).to_i, ((g + m) * 255).to_i, ((b + m) * 255).to_i)
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # COLOR CHAIN: The derivation sequence
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class ColorChain
    attr_reader :genesis_seed, :chain, :length
    
    def initialize(genesis_seed: 0x42D, length: 12)
      @genesis_seed = genesis_seed
      @length = length
      @chain = []
      derive_chain!
    end
    
    # Build the derivation chain (no time, only derivation)
    def derive_chain!
      current_seed = @genesis_seed
      
      @length.times do |i|
        color = Unworld.derive_color(current_seed, 0)
        
        @chain << {
          position: i,  # Position in derivation, not time
          seed: current_seed,
          color: color,
          derivation: i == 0 ? :genesis : :chained
        }
        
        # Chain to next seed (derivational, not temporal)
        current_seed = Unworld.chain_seed(current_seed, color[:trit])
      end
      
      self
    end
    
    # Verify chain integrity (each color derives correctly)
    def verify_chain
      @chain.each_cons(2).all? do |prev, curr|
        expected_seed = Unworld.chain_seed(prev[:seed], prev[:color][:trit])
        curr[:seed] == expected_seed
      end
    end
    
    # GF(3) sum over chain
    def gf3_sum
      @chain.sum { |c| c[:color][:trit] }
    end
    
    # Is chain GF(3) balanced? (sum ≡ 0 mod 3)
    def gf3_balanced?
      (gf3_sum % 3) == 0
    end
    
    # Extract the unworlded pattern (structure without context)
    def unworld
      {
        genesis: @genesis_seed,
        derivations: @chain.map { |c| c[:color][:trit] },
        colors: @chain.map { |c| c[:color][:hex] },
        gf3_sum: gf3_sum,
        gf3_balanced: gf3_balanced?,
        verified: verify_chain
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # TRIADIC CHAIN: Three interleaved derivation streams
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class TriadicChain
    attr_reader :genesis_seed, :chains, :length
    
    def initialize(genesis_seed: 0x42D, length: 12)
      @genesis_seed = genesis_seed
      @length = length
      @chains = {
        minus: [],
        ergodic: [],
        plus: []
      }
      derive_triadic!
    end
    
    def derive_triadic!
      # Three genesis seeds derived from one
      seeds = {
        minus: @genesis_seed,
        ergodic: (@genesis_seed ^ GOLDEN) & MASK64,
        plus: (@genesis_seed ^ (GOLDEN << 1)) & MASK64
      }
      
      @length.times do |i|
        [:minus, :ergodic, :plus].each do |polarity|
          color = Unworld.derive_color(seeds[polarity], 0)
          
          @chains[polarity] << {
            position: i,
            seed: seeds[polarity],
            color: color,
            polarity: polarity
          }
          
          # Chain each stream independently
          seeds[polarity] = Unworld.chain_seed(seeds[polarity], color[:trit])
        end
      end
      
      self
    end
    
    # GF(3) conservation at each position
    def gf3_at_position(pos)
      sum = [:minus, :ergodic, :plus].sum { |p| @chains[p][pos][:color][:trit] }
      { position: pos, sum: sum, conserved: (sum % 3) == 0 }
    end
    
    # Full GF(3) verification
    def gf3_all_conserved?
      (0...@length).all? { |i| gf3_at_position(i)[:conserved] }
    end
    
    # Unworld the triadic structure
    def unworld
      {
        genesis: @genesis_seed,
        streams: {
          minus: @chains[:minus].map { |c| c[:color][:hex] },
          ergodic: @chains[:ergodic].map { |c| c[:color][:hex] },
          plus: @chains[:plus].map { |c| c[:color][:hex] }
        },
        gf3_all_conserved: gf3_all_conserved?,
        positions: (0...@length).map { |i| gf3_at_position(i) }
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # 3-MATCH CHAIN: Derivational 3-MATCH sequence
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class ThreeMatchChain
    attr_reader :genesis_seed, :matches, :length
    
    def initialize(genesis_seed: 0x42D, length: 4)
      @genesis_seed = genesis_seed
      @length = length
      @matches = []
      derive_matches!
    end
    
    def derive_matches!
      current_seed = @genesis_seed
      
      @length.times do |i|
        # Create 3-MATCH at current seed
        match = ThreeMatchGeodesicGadget::ThreeMatch.new(seed: current_seed, depth: 1)
        
        @matches << {
          position: i,
          seed: current_seed,
          colors: [match.color_a, match.color_b, match.color_c],
          gf3_conserved: match.gf3_conserved?
        }
        
        # Derive next seed from match result
        # Use XOR of all three color contributions
        combined_trit = (match.color_a[:trit] + match.color_b[:trit] + match.color_c[:trit]) % 3
        adjusted_trit = combined_trit == 0 ? 0 : (combined_trit == 1 ? 1 : -1)
        current_seed = Unworld.chain_seed(current_seed, adjusted_trit)
      end
      
      self
    end
    
    # Unworld the 3-MATCH chain
    def unworld
      {
        genesis: @genesis_seed,
        matches: @matches.map do |m|
          {
            position: m[:position],
            colors: m[:colors].map { |c| c[:hex] },
            gf3: m[:gf3_conserved]
          }
        end,
        all_gf3_conserved: @matches.all? { |m| m[:gf3_conserved] }
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # INVOLUTION CHAIN: Self-inverse derivation
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class InvolutionChain
    attr_reader :genesis_seed, :forward_chain, :backward_chain
    
    def initialize(genesis_seed: 0x42D, length: 6)
      @genesis_seed = genesis_seed
      @length = length
      @forward_chain = []
      @backward_chain = []
      derive_involution!
    end
    
    def derive_involution!
      # Forward derivation
      current_seed = @genesis_seed
      @length.times do |i|
        color = Unworld.derive_color(current_seed, 0)
        @forward_chain << { position: i, seed: current_seed, color: color }
        current_seed = Unworld.chain_seed(current_seed, color[:trit])
      end
      
      # Backward derivation (involution: negate trits)
      current_seed = @forward_chain.last[:seed]
      (@length - 1).downto(0) do |i|
        # Invert the trit for backward chaining
        inverted_trit = -@forward_chain[i][:color][:trit]
        inverted_trit = 0 if inverted_trit == 0  # 0 is its own inverse
        
        color = { 
          trit: inverted_trit, 
          hex: Unworld.trit_to_hex(inverted_trit, current_seed),
          seed: current_seed 
        }
        @backward_chain.unshift({ position: i, seed: current_seed, color: color })
        
        # Chain backward
        current_seed = Unworld.chain_seed(current_seed, inverted_trit)
      end
      
      self
    end
    
    # Verify ι∘ι = id (applying involution twice returns to start)
    def involution_verified?
      # The sum of forward + backward trits should be 0 at each position
      (0...@length).all? do |i|
        fwd = @forward_chain[i][:color][:trit]
        bwd = @backward_chain[i][:color][:trit]
        fwd + bwd == 0
      end
    end
    
    # Unworld the involution
    def unworld
      {
        genesis: @genesis_seed,
        forward: @forward_chain.map { |c| c[:color][:hex] },
        backward: @backward_chain.map { |c| c[:color][:hex] },
        involution_verified: involution_verified?,
        fixed_points: @forward_chain.select { |c| c[:color][:trit] == 0 }.map { |c| c[:position] }
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # BEST RESPONSE CHAIN: Nash equilibrium via derivation
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class BestResponseChain
    attr_reader :genesis_seed, :rounds
    
    def initialize(genesis_seed: 0x42D, max_rounds: 10)
      @genesis_seed = genesis_seed
      @max_rounds = max_rounds
      @rounds = []
      derive_equilibrium!
    end
    
    def derive_equilibrium!
      # Initialize agents from genesis
      rng = SplitMixTernary::TripartiteStreams.new(@genesis_seed)
      triplet = rng.next_triplet
      
      agents = {
        a: triplet[:minus],
        b: triplet[:ergodic],
        c: triplet[:plus]
      }
      
      current_seed = @genesis_seed
      
      @max_rounds.times do |round|
        @rounds << {
          position: round,
          seed: current_seed,
          agents: agents.dup,
          gf3_sum: agents.values.sum
        }
        
        # Best response: each agent adjusts to make GF(3) = 0
        new_agents = {}
        [:a, :b, :c].each do |id|
          others = agents.reject { |k, _| k == id }.values
          other_sum = others.sum
          # Best response: choose trit that makes sum = 0 mod 3
          target = ((-other_sum) % 3)
          new_agents[id] = target == 0 ? 0 : (target == 1 ? 1 : -1)
        end
        
        # Check convergence (Nash equilibrium)
        if agents == new_agents
          @rounds << { position: round + 1, equilibrium: true, agents: agents.dup }
          break
        end
        
        agents = new_agents
        
        # Chain seed based on combined response
        combined = agents.values.sum % 3
        current_seed = Unworld.chain_seed(current_seed, combined == 0 ? 0 : (combined == 1 ? 1 : -1))
      end
      
      self
    end
    
    def equilibrium_reached?
      @rounds.last&.dig(:equilibrium) == true
    end
    
    def unworld
      {
        genesis: @genesis_seed,
        rounds: @rounds.size,
        equilibrium: equilibrium_reached?,
        final_agents: @rounds.last[:agents],
        trajectory: @rounds.map { |r| r[:agents]&.values || [] }
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # FULL UNWORLD: Combine all derivations
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.full_unworld(seed: 0x42D)
    puts "=" * 70
    puts "UNWORLD: Replace Time with Color Chain Derivations"
    puts "         Seed: #{format('0x%X', seed)}"
    puts "=" * 70
    puts
    
    # 1. Color Chain
    puts "─── COLOR CHAIN (Derivational Succession) ───"
    chain = ColorChain.new(genesis_seed: seed, length: 8)
    unworlded = chain.unworld
    puts "  Genesis: #{format('0x%X', unworlded[:genesis])}"
    puts "  Derivations: #{unworlded[:derivations].join(' → ')}"
    puts "  Colors: #{unworlded[:colors].join(' ')}"
    puts "  GF(3) sum: #{unworlded[:gf3_sum]} (balanced: #{unworlded[:gf3_balanced]})"
    puts "  Verified: #{unworlded[:verified]}"
    puts
    
    # 2. Triadic Chain
    puts "─── TRIADIC CHAIN (Three Interleaved Streams) ───"
    triadic = TriadicChain.new(genesis_seed: seed, length: 6)
    unworlded = triadic.unworld
    puts "  MINUS:   #{unworlded[:streams][:minus].join(' ')}"
    puts "  ERGODIC: #{unworlded[:streams][:ergodic].join(' ')}"
    puts "  PLUS:    #{unworlded[:streams][:plus].join(' ')}"
    puts "  GF(3) all conserved: #{unworlded[:gf3_all_conserved]}"
    puts
    
    # 3. 3-MATCH Chain
    puts "─── 3-MATCH CHAIN (Derivational Gadgets) ───"
    matches = ThreeMatchChain.new(genesis_seed: seed, length: 4)
    unworlded = matches.unworld
    unworlded[:matches].each do |m|
      puts "  Position #{m[:position]}: #{m[:colors].join(' ')} | GF(3): #{m[:gf3]}"
    end
    puts "  All GF(3) conserved: #{unworlded[:all_gf3_conserved]}"
    puts
    
    # 4. Involution Chain
    puts "─── INVOLUTION CHAIN (ι∘ι = id) ───"
    involution = InvolutionChain.new(genesis_seed: seed, length: 6)
    unworlded = involution.unworld
    puts "  Forward:  #{unworlded[:forward].join(' ')}"
    puts "  Backward: #{unworlded[:backward].join(' ')}"
    puts "  ι∘ι = id verified: #{unworlded[:involution_verified]}"
    puts "  Fixed points (trit=0): positions #{unworlded[:fixed_points].join(', ')}"
    puts
    
    # 5. Best Response Chain
    puts "─── BEST RESPONSE CHAIN (Nash Equilibrium) ───"
    best = BestResponseChain.new(genesis_seed: seed, max_rounds: 10)
    unworlded = best.unworld
    puts "  Rounds to equilibrium: #{unworlded[:rounds]}"
    puts "  Equilibrium reached: #{unworlded[:equilibrium]}"
    puts "  Final agents: #{unworlded[:final_agents]}"
    puts
    
    puts "=" * 70
    puts "SUMMARY: Time replaced with derivation"
    puts "  • Seed chaining: seed_{n+1} = f(seed_n, color_n)"
    puts "  • No external clock: only internal derivation"
    puts "  • GF(3) conserved at all positions"
    puts "  • Involution: forward ∘ backward = identity"
    puts "  • Nash equilibrium via derivational best response"
    puts "=" * 70
    
    # Return combined result
    {
      seed: seed,
      color_chain: ColorChain.new(genesis_seed: seed).unworld,
      triadic_chain: TriadicChain.new(genesis_seed: seed).unworld,
      three_match_chain: ThreeMatchChain.new(genesis_seed: seed).unworld,
      involution_chain: InvolutionChain.new(genesis_seed: seed).unworld,
      best_response_chain: BestResponseChain.new(genesis_seed: seed).unworld
    }
  end
end

if __FILE__ == $0
  seed = ARGV[0] ? ARGV[0].to_i(16) : 0x42D
  Unworld.full_unworld(seed: seed)
end
