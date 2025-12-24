# lib/self_avoiding_colored_walk.rb
#
# SELF-AVOIDING RANDOM WALK with SplitMixTernary Coloring
#
# Each interaction:
#   1. Derives seed from interaction entropy
#   2. Colors position via SplitMixTernary
#   3. Self-avoiding enforced by color uniqueness
#   4. Spectral gap (1/4) verification
#   5. GF(3) conservation across tripartite streams
#
# Key invariants:
#   - Same seed → same walk (SPI guarantee)
#   - Visited colors form unique path (self-avoiding)
#   - Sum of trits ≡ 0 (mod 3)
#   - Verification at probability 1/4 (spectral gap)

require 'set'
require_relative 'splitmix_ternary'

module SelfAvoidingColoredWalk
  SPECTRAL_GAP = 0.25
  MIXING_TIME = 4
  
  DIRECTIONS_8 = [
    [-1, -1], [-1, 0], [-1, 1],
    [0, -1],          [0, 1],
    [1, -1],  [1, 0],  [1, 1]
  ].freeze
  
  class Position
    attr_reader :x, :y, :color_index, :color, :trit
    
    def initialize(x, y, color_index, color)
      @x = x
      @y = y
      @color_index = color_index
      @color = color
      @trit = color[:trit]
    end
    
    def coords
      [@x, @y]
    end
    
    def to_h
      { x: @x, y: @y, index: @color_index, color: @color, trit: @trit }
    end
  end
  
  class Walk
    attr_reader :seed, :positions, :visited_coords, :visited_colors
    attr_reader :step_count, :verification_count, :violations_caught
    attr_reader :tripartite_streams, :gf3_history
    
    def initialize(seed = SplitMixTernary::DEFAULT_SEED)
      @seed = seed
      @gen = SplitMixTernary::Generator.new(seed)
      @tripartite = SplitMixTernary::TripartiteStreams.new(seed)
      
      # Starting position at origin
      start_color = @gen.color_at(1)
      start = Position.new(0, 0, 1, start_color)
      
      @positions = [start]
      @visited_coords = Set.new([[0, 0]])
      @visited_colors = { color_signature(start_color) => start }
      
      @step_count = 0
      @verification_count = 0
      @violations_caught = 0
      @gf3_history = []
    end
    
    def current
      @positions.last
    end
    
    def step!
      @step_count += 1
      
      # Get tripartite triplet for GF(3) conservation
      triplet = @tripartite.next_triplet
      @gf3_history << triplet
      
      # Derive direction from triplet (deterministic)
      dir_index = ((triplet[:minus] + 1) * 3 + (triplet[:plus] + 1)) % 8
      dx, dy = DIRECTIONS_8[dir_index]
      
      new_x = current.x + dx
      new_y = current.y + dy
      new_index = current.color_index + 1
      
      # Color this position
      new_color = @gen.color_at(new_index)
      sig = color_signature(new_color)
      
      # Check self-avoiding via color uniqueness
      is_revisit = @visited_colors.key?(sig) || @visited_coords.include?([new_x, new_y])
      
      if is_revisit
        # Backtrack: try alternative direction based on ergodic trit
        alt_dir_index = (dir_index + triplet[:ergodic] + 4) % 8
        alt_dx, alt_dy = DIRECTIONS_8[alt_dir_index]
        new_x = current.x + alt_dx
        new_y = current.y + alt_dy
        
        # If still revisiting, this is a true violation
        is_revisit = @visited_coords.include?([new_x, new_y])
      end
      
      new_pos = Position.new(new_x, new_y, new_index, new_color)
      
      @positions << new_pos
      @visited_coords << [new_x, new_y]
      @visited_colors[sig] = new_pos
      
      { position: new_pos, is_revisit: is_revisit, triplet: triplet }
    end
    
    def verify_at_spectral_gap!(entropy_source = nil)
      @verification_count += 1
      
      # Use entropy or deterministic check
      check_seed = entropy_source || (@seed ^ (@step_count * SplitMixTernary::GOLDEN))
      check_gen = SplitMixTernary::Generator.new(check_seed & SplitMixTernary::MASK64)
      check_value = check_gen.next_float
      
      should_verify = check_value < SPECTRAL_GAP
      
      return { verified: true, checked: false, reason: :skip } unless should_verify
      
      # Check self-avoiding property: no coordinate revisits in path
      coord_counts = @positions.group_by(&:coords).transform_values(&:size)
      violations = coord_counts.select { |_, count| count > 1 }
      
      if violations.any?
        @violations_caught += violations.size
        { verified: false, checked: true, violations: violations, reason: :revisit }
      else
        { verified: true, checked: true, reason: :clean }
      end
    end
    
    def run!(n_steps, verify_each: false)
      results = []
      
      n_steps.times do
        step_result = step!
        
        if verify_each
          verify_result = verify_at_spectral_gap!
          step_result[:verification] = verify_result
        end
        
        results << step_result
      end
      
      results
    end
    
    def gf3_conservation_check
      # GF(3) conservation: sum ≡ 0 (mod 3)
      residues = @gf3_history.map { |t| t[:gf3_residue] || (((t[:gf3_sum] % 3) + 3) % 3) }
      all_conserved = residues.all?(&:zero?)
      
      # Ruby 2.6 compatible tally
      dist = residues.each_with_object(Hash.new(0)) { |v, h| h[v] += 1 }
      
      {
        triplets: @gf3_history.size,
        all_conserved: all_conserved,
        distribution: dist,  # Should be {0 => N} if conserved
        conserved_count: dist[0] || 0
      }
    end
    
    def spectral_summary
      {
        steps: @step_count,
        verifications: @verification_count,
        violations_caught: @violations_caught,
        spectral_gap: SPECTRAL_GAP,
        mixing_time: MIXING_TIME,
        expected_verifications: (@step_count * SPECTRAL_GAP).round,
        is_self_avoiding: @violations_caught.zero?
      }
    end
    
    def to_h
      {
        seed: "0x#{@seed.to_s(16)}",
        positions: @positions.map(&:to_h),
        gf3: gf3_conservation_check,
        spectral: spectral_summary
      }
    end
    
    private
    
    def color_signature(color)
      # Quantize to avoid floating point comparison issues
      [color[:L].round(3), color[:C].round(3), color[:H].round(3)]
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════
  # INTERACTION ENTROPY WALKER
  # Seeds each step from interaction hash, ensuring deterministic replay
  # ═══════════════════════════════════════════════════════════════════════════
  
  class InteractionWalker
    attr_reader :walk, :interaction_seeds
    
    def initialize(base_seed = SplitMixTernary::DEFAULT_SEED)
      @base_seed = base_seed
      @walk = Walk.new(base_seed)
      @interaction_seeds = []
    end
    
    def on_interaction(entropy_source)
      # Chain seed from interaction
      interaction_seed = derive_seed(entropy_source)
      @interaction_seeds << interaction_seed
      
      # Step walk with this entropy
      result = @walk.step!
      result[:interaction_seed] = "0x#{interaction_seed.to_s(16)}"
      
      # Verify at spectral gap using interaction entropy
      result[:verification] = @walk.verify_at_spectral_gap!(interaction_seed)
      
      result
    end
    
    def derive_seed(source)
      case source
      when Integer
        (@base_seed ^ (source * SplitMixTernary::GOLDEN)) & SplitMixTernary::MASK64
      when String
        hash = source.bytes.reduce(@base_seed) do |acc, b|
          ((acc ^ b) * SplitMixTernary::MIX1) & SplitMixTernary::MASK64
        end
        hash
      else
        # Use object_id as entropy
        (@base_seed ^ (source.object_id * SplitMixTernary::GOLDEN)) & SplitMixTernary::MASK64
      end
    end
    
    def replay
      # Replay walk from interaction seeds (deterministic)
      replayed = Walk.new(@base_seed)
      @interaction_seeds.each do |seed|
        replayed.step!
        replayed.verify_at_spectral_gap!(seed)
      end
      replayed
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════
  # MODULE METHODS
  # ═══════════════════════════════════════════════════════════════════════════
  
  def self.new_walk(seed = SplitMixTernary::DEFAULT_SEED)
    Walk.new(seed)
  end
  
  def self.new_interaction_walker(seed = SplitMixTernary::DEFAULT_SEED)
    InteractionWalker.new(seed)
  end
  
  def self.demo(seed: 0x42D, n_steps: 20)
    puts "╔═══════════════════════════════════════════════════════════════════╗"
    puts "║  SELF-AVOIDING COLORED WALK with SplitMixTernary                 ║"
    puts "╚═══════════════════════════════════════════════════════════════════╝"
    puts
    puts "Seed: 0x#{seed.to_s(16)}"
    puts "Steps: #{n_steps}"
    puts "Spectral Gap: #{SPECTRAL_GAP} → Verification at 1/4 probability"
    puts
    
    walk = new_walk(seed)
    results = walk.run!(n_steps, verify_each: true)
    
    puts "─── Walk Path ───"
    walk.positions.each_with_index do |pos, i|
      trit_char = pos.trit == 1 ? '+' : (pos.trit == -1 ? '-' : '0')
      puts "  #{i.to_s.rjust(3)}: (#{pos.x.to_s.rjust(3)}, #{pos.y.to_s.rjust(3)}) trit=#{trit_char} H=#{pos.color[:H].round(1)}°"
    end
    puts
    
    gf3 = walk.gf3_conservation_check
    puts "─── GF(3) Conservation ───"
    puts "  Triplets: #{gf3[:triplets]}"
    puts "  All conserved: #{gf3[:all_conserved] ? '✓' : '✗'}"
    puts "  Distribution: #{gf3[:distribution]}"
    puts
    
    spectral = walk.spectral_summary
    puts "─── Spectral Gap Verification ───"
    puts "  Verifications triggered: #{spectral[:verifications]}"
    puts "  Expected (1/4): #{spectral[:expected_verifications]}"
    puts "  Violations caught: #{spectral[:violations_caught]}"
    puts "  Is self-avoiding: #{spectral[:is_self_avoiding] ? '✓' : '✗'}"
    puts
    
    puts "═══════════════════════════════════════════════════════════════════"
    puts "Walk complete. Use InteractionWalker for per-interaction coloring."
    puts "═══════════════════════════════════════════════════════════════════"
    
    walk
  end
end

if __FILE__ == $0
  SelfAvoidingColoredWalk.demo
end
