# lib/xoroshiro_3color.rb
#
# 3-COLOR STREAMS: Correct by Construction 3-Coloring
#
# Uses xoroshiro128** ONLY FOR SEEDING to create 3 independent seed streams
# All actual color generation goes through Gay.jl SplitMix64 algorithm
#
# Architecture:
#   xoroshiro128** → generates 3 independent seeds via jump()
#   Gay SplitMix64 → generates colors from those seeds (canonical algorithm)
#
# color://stream/minus   → Trit -1 (Cold: H ∈ [180°, 300°))
# color://stream/ergodic → Trit  0 (Neutral: H ∈ [60°, 180°))
# color://stream/plus    → Trit +1 (Warm: H ∈ [0°, 60°) ∪ [300°, 360°))

require_relative 'girard_colors'  # For SeedMiner (Gay SplitMix64)

module Xoroshiro3Color
  # Xoroshiro128** constants - ONLY used for seed generation
  ROTL_A = 24
  ROTL_B = 16
  SHIFT_A = 37
  SHIFT_B = 7
  SHIFT_C = 17
  
  MASK64 = 0xFFFFFFFFFFFFFFFF
  
  # Rotation helper
  def self.rotl(x, k)
    ((x << k) | (x >> (64 - k))) & MASK64
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # XOROSHIRO128** - ONLY FOR SEED GENERATION (not color generation!)
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class Xoroshiro128StarStar
    attr_reader :s0, :s1
    
    def initialize(seed)
      # Initialize with SplitMix64 to avoid poor seeding
      @s0 = splitmix64_init(seed)
      @s1 = splitmix64_init(@s0)
    end
    
    def splitmix64_init(x)
      z = (x + 0x9e3779b97f4a7c15) & MASK64
      z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK64
      z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK64
      (z ^ (z >> 31)) & MASK64
    end
    
    def next_u64
      result = Xoroshiro3Color.rotl((@s0 * 5) & MASK64, 7)
      result = (result * 9) & MASK64
      
      t = (@s1 ^ @s0) & MASK64
      @s0 = (Xoroshiro3Color.rotl(@s0, ROTL_A) ^ t ^ ((t << SHIFT_A) & MASK64)) & MASK64
      @s1 = Xoroshiro3Color.rotl(t, ROTL_B)
      
      result
    end
    
    # Jump 2^64 steps - creates independent streams
    def jump
      jump_const = [0xdf900294d8f554a5, 0x170865df4b3201fc]
      s0 = 0
      s1 = 0
      
      jump_const.each do |jc|
        64.times do |b|
          if (jc & (1 << b)) != 0
            s0 ^= @s0
            s1 ^= @s1
          end
          next_u64
        end
      end
      
      @s0 = s0 & MASK64
      @s1 = s1 & MASK64
      self
    end
    
    # Long jump 2^96 steps
    def long_jump
      jump_const = [0xd2a98b26625eee7b, 0xdddf9b1090aa7ac1]
      s0 = 0
      s1 = 0
      
      jump_const.each do |jc|
        64.times do |b|
          if (jc & (1 << b)) != 0
            s0 ^= @s0
            s1 ^= @s1
          end
          next_u64
        end
      end
      
      @s0 = s0 & MASK64
      @s1 = s1 & MASK64
      self
    end
    
    # Clone for independent stream
    def fork
      forked = Xoroshiro128StarStar.allocate
      forked.instance_variable_set(:@s0, @s0)
      forked.instance_variable_set(:@s1, @s1)
      forked
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # 3-COLOR STREAM: Correct by Construction
  # xoroshiro ONLY for seed derivation → Gay SplitMix64 for actual colors
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class ColorStream
    HUE_RANGES = {
      minus:   [180, 300],  # Cold: cyan/blue/purple
      ergodic: [60, 180],   # Neutral: yellow/green/cyan
      plus:    [[0, 60], [300, 360]]  # Warm: red/orange/magenta
    }.freeze
    
    TRIT_MAP = { minus: -1, ergodic: 0, plus: 1 }.freeze
    
    attr_reader :polarity, :trit, :stream_seed, :index
    
    def initialize(polarity, master_seed)
      @polarity = polarity
      @trit = TRIT_MAP[polarity]
      @index = 0
      
      # Use xoroshiro ONLY to derive independent seed for Gay
      seed_gen = Xoroshiro128StarStar.new(master_seed)
      case polarity
      when :minus
        # No jump - first stream seed
      when :ergodic
        seed_gen.jump  # Jump 2^64 for independent seed
      when :plus
        seed_gen.jump.jump  # Jump 2^128 for independent seed
      end
      
      # Extract stream seed from xoroshiro, then ONLY use Gay from here
      @stream_seed = (seed_gen.s0 ^ seed_gen.s1) & MASK64
    end
    
    # Generate next color using Gay SplitMix64, then constrain hue
    def next_color
      @index += 1
      
      # Gay.jl canonical color generation
      raw_color = SeedMiner.color_at(@stream_seed, @index)
      
      # Constrain hue to this stream's range (preserves L, C from Gay)
      constrained_h = constrain_hue(raw_color[:H])
      
      {
        index: @index,
        polarity: @polarity,
        trit: @trit,
        L: raw_color[:L],
        C: raw_color[:C],
        H: constrained_h,
        hex: SeedMiner.lch_to_hex(raw_color[:L], raw_color[:C], constrained_h),
        gay_seed: @stream_seed,
        raw_H: raw_color[:H]
      }
    end
    
    # Get color at specific index (stateless via Gay)
    def color_at(idx)
      raw_color = SeedMiner.color_at(@stream_seed, idx)
      constrained_h = constrain_hue(raw_color[:H])
      
      {
        index: idx,
        polarity: @polarity,
        trit: @trit,
        L: raw_color[:L],
        C: raw_color[:C],
        H: constrained_h,
        hex: SeedMiner.lch_to_hex(raw_color[:L], raw_color[:C], constrained_h),
        gay_seed: @stream_seed
      }
    end
    
    private
    
    # Map hue from Gay to this stream's constrained range
    def constrain_hue(h)
      range = HUE_RANGES[@polarity]
      
      if range.is_a?(Array) && range[0].is_a?(Array)
        # Plus: two ranges [0,60) and [300,360)
        span1 = range[0][1] - range[0][0]
        span2 = range[1][1] - range[1][0]
        total = span1 + span2
        normalized = (h % 360.0) / 360.0 * total
        
        if normalized < span1
          range[0][0] + normalized
        else
          range[1][0] + (normalized - span1)
        end
      else
        # Single range
        span = range[1] - range[0]
        range[0] + ((h % 360.0) / 360.0 * span)
      end
    end
  end
  
  # Compatibility: LCH to hex (delegates to SeedMiner if available)
  def self.lch_to_hex(l, c, h)
    if defined?(SeedMiner) && SeedMiner.respond_to?(:lch_to_hex)
      SeedMiner.lch_to_hex(l, c, h)
    else
      # Fallback
      h_rad = h * Math::PI / 180
      a = c * Math.cos(h_rad) * 0.01
      b = c * Math.sin(h_rad) * 0.01
      l_norm = l / 100.0
      
      r = [[l_norm + a, 0].max, 1].min
      g = [[l_norm - 0.5 * a.abs - 0.5 * b.abs, 0].max, 1].min
      bl = [[l_norm + b, 0].max, 1].min
      
      "#%02X%02X%02X" % [(r * 255).round, (g * 255).round, (bl * 255).round]
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # TRIPARTITE SYSTEM: 3 Independent Gay Streams with GF(3) Conservation
  # xoroshiro generates 3 independent seeds → each stream uses Gay SplitMix64
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class TripartiteStreams
    attr_reader :minus, :ergodic, :plus, :history
    
    def initialize(seed = 0x6761795f636f6c6f)
      @seed = seed
      @minus = ColorStream.new(:minus, seed)
      @ergodic = ColorStream.new(:ergodic, seed)
      @plus = ColorStream.new(:plus, seed)
      @history = []
    end
    
    # Generate one color from each stream (GF(3) conserved by construction)
    def next_triplet
      triplet = {
        minus: @minus.next_color,
        ergodic: @ergodic.next_color,
        plus: @plus.next_color,
        gf3_sum: -1 + 0 + 1,  # Always 0
        conserved: true
      }
      @history << triplet
      triplet
    end
    
    # Get triplet at specific index
    def triplet_at(idx)
      {
        minus: @minus.color_at(idx),
        ergodic: @ergodic.color_at(idx),
        plus: @plus.color_at(idx),
        gf3_sum: 0,
        conserved: true
      }
    end
    
    # Generate N triplets
    def generate(n)
      n.times.map { next_triplet }
    end
    
    # Verify GF(3) conservation (always true by construction)
    def verify_conservation
      @history.all? { |t| t[:gf3_sum] % 3 == 0 }
    end
    
    # URI accessor: color://stream/{polarity}
    def resolve_uri(uri)
      case uri
      when %r{^color://stream/minus$}
        @minus.next_color
      when %r{^color://stream/ergodic$}
        @ergodic.next_color
      when %r{^color://stream/plus$}
        @plus.next_color
      when %r{^color://stream/minus/(\d+)$}
        @minus.color_at($1.to_i)
      when %r{^color://stream/ergodic/(\d+)$}
        @ergodic.color_at($1.to_i)
      when %r{^color://stream/plus/(\d+)$}
        @plus.color_at($1.to_i)
      when %r{^color://triplet$}
        next_triplet
      when %r{^color://triplet/(\d+)$}
        triplet_at($1.to_i)
      else
        raise ArgumentError, "Unknown URI: #{uri}"
      end
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # REWRITING GADGET: 3-Color Matching
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class RewritingGadget
    # A rewriting rule that preserves 3-coloring
    Rule = Struct.new(:name, :pattern, :replacement, :color_constraint)
    
    attr_reader :streams, :rules
    
    def initialize(seed = 0x42D)
      @streams = TripartiteStreams.new(seed)
      @rules = []
    end
    
    # Add a rewriting rule with color constraint
    def add_rule(name, pattern, replacement, required_trit: nil)
      @rules << Rule.new(name, pattern, replacement, required_trit)
    end
    
    # Apply rules to a colored term
    def rewrite(term, max_steps: 100)
      current = term
      steps = []
      
      max_steps.times do |i|
        # Get color for this step
        triplet = @streams.next_triplet
        step_trit = case i % 3
                    when 0 then -1
                    when 1 then 0
                    when 2 then 1
                    end
        
        # Find applicable rule
        rule = @rules.find do |r|
          matches_pattern?(current, r.pattern) &&
            (r.color_constraint.nil? || r.color_constraint == step_trit)
        end
        
        break unless rule
        
        # Apply rewrite
        new_term = apply_rule(current, rule)
        steps << {
          step: i + 1,
          rule: rule.name,
          from: current,
          to: new_term,
          trit: step_trit,
          color: triplet[%i[minus ergodic plus][step_trit + 1]]
        }
        current = new_term
      end
      
      { result: current, steps: steps, gf3_conserved: @streams.verify_conservation }
    end
    
    private
    
    def matches_pattern?(term, pattern)
      term.include?(pattern) || pattern.is_a?(Regexp) && term.match?(pattern)
    end
    
    def apply_rule(term, rule)
      term.sub(rule.pattern, rule.replacement)
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # DEMONSTRATION
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.demo(seed: 0x42D, n: 6)
    puts "╔═══════════════════════════════════════════════════════════════════╗"
    puts "║  GAY 3-COLOR STREAMS: Correct by Construction                    ║"
    puts "╚═══════════════════════════════════════════════════════════════════╝"
    puts
    puts "Master Seed: 0x#{seed.to_s(16)}"
    puts "Architecture: xoroshiro128** → 3 seeds → Gay SplitMix64 → colors"
    puts
    
    streams = TripartiteStreams.new(seed)
    
    puts "─── Three Independent Streams (GF(3) = 0 by construction) ───"
    puts
    puts "color://stream/minus   → Trit -1 (Cold: H ∈ [180°, 300°))"
    puts "color://stream/ergodic → Trit  0 (Neutral: H ∈ [60°, 180°))"
    puts "color://stream/plus    → Trit +1 (Warm: H ∈ [0°, 60°) ∪ [300°, 360°))"
    puts
    
    puts "─── Generated Triplets ───"
    puts
    
    triplets = streams.generate(n)
    triplets.each_with_index do |t, i|
      m = t[:minus]
      e = t[:ergodic]
      p = t[:plus]
      
      puts "Triplet #{i + 1}:"
      puts "  MINUS:   #{m[:hex]} H=#{m[:H].round(1)}° (trit: #{m[:trit]})"
      puts "  ERGODIC: #{e[:hex]} H=#{e[:H].round(1)}° (trit: #{e[:trit]})"
      puts "  PLUS:    #{p[:hex]} H=#{p[:H].round(1)}° (trit: #{p[:trit]})"
      puts "  GF(3): #{m[:trit]} + #{e[:trit]} + #{p[:trit]} = #{t[:gf3_sum]} ≡ 0 (mod 3) ✓"
      puts
    end
    
    puts "─── URI Resolution ───"
    puts
    puts "color://stream/minus/5  → #{streams.resolve_uri('color://stream/minus/5')[:hex]}"
    puts "color://stream/ergodic/5 → #{streams.resolve_uri('color://stream/ergodic/5')[:hex]}"
    puts "color://stream/plus/5   → #{streams.resolve_uri('color://stream/plus/5')[:hex]}"
    puts
    
    puts "─── Rewriting Gadget Demo ───"
    puts
    
    gadget = RewritingGadget.new(seed)
    gadget.add_rule("expand-f", "f(x)", "g(h(x))", required_trit: -1)
    gadget.add_rule("simplify-h", "h(x)", "x", required_trit: 0)
    gadget.add_rule("wrap-g", "g(", "wrap(g(", required_trit: 1)
    
    result = gadget.rewrite("f(x)", max_steps: 6)
    puts "Initial: f(x)"
    result[:steps].each do |s|
      puts "  Step #{s[:step]} [trit: #{s[:trit]}]: #{s[:from]} → #{s[:to]} (#{s[:rule]})"
    end
    puts "Result: #{result[:result]}"
    puts "GF(3) conserved: #{result[:gf3_conserved]}"
    
    puts
    puts "═══════════════════════════════════════════════════════════════════"
    puts "Architecture: xoroshiro128** ONLY seeds Gay SplitMix64"
    puts "  1. xoroshiro.jump() → 3 independent seeds (2^64 apart)"
    puts "  2. Gay SplitMix64 generates all colors from those seeds"
    puts "  3. Hue constrained to stream range (L, C preserved from Gay)"
    puts "═══════════════════════════════════════════════════════════════════"
  end
end

if __FILE__ == $0
  Xoroshiro3Color.demo
end
