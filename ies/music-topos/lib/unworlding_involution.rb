# lib/unworlding_involution.rb
#
# Unworlding Involution: Frame-Invariant Self via Best Response Color Dynamics
#
# Core concepts:
# 1. Unworlding: Extract structure from demo without evaluation context
# 2. Involution: ι∘ι = id (self-inverse transformation)
# 3. Frame invariance: Same dynamics from any agent's perspective
# 4. Best response: GF(3)-conserving Nash equilibrium in 3-MATCH
#
# The "self" is the seed - invariant across all observation frames.

require_relative 'splitmix_ternary'
require_relative 'three_match_geodesic_gadget'

module UnworldingInvolution
  # ═══════════════════════════════════════════════════════════════════════════════
  # INVOLUTION: ι∘ι = id
  # ═══════════════════════════════════════════════════════════════════════════════
  
  # An involution is its own inverse: apply twice → return to start
  class Involution
    attr_reader :state, :seed, :history
    
    def initialize(seed: 0x42D)
      @seed = seed
      @state = :original
      @color = generate_color(0)
      @history = [{ state: @state, color: @color }]
    end
    
    # Apply involution: original ↔ inverted
    def apply!
      @state = (@state == :original) ? :inverted : :original
      # Involution on color: negate the trit
      @color = {
        trit: -@color[:trit],
        hex: invert_hex(@color[:hex]),
        index: @color[:index]
      }
      @history << { state: @state, color: @color }
      self
    end
    
    # Verify ι∘ι = id
    def self_inverse?
      original_state = @state
      original_color = @color.dup
      
      apply!  # ι
      apply!  # ι∘ι
      
      result = (@state == original_state) && (@color[:trit] == original_color[:trit])
      
      # Reset
      @state = original_state
      @color = original_color
      
      result
    end
    
    # The fixed point of involution
    def fixed_point
      # ι(x) = x implies x is ergodic (trit = 0)
      { trit: 0, hex: "#808080", meaning: "ERGODIC is fixed point of involution" }
    end
    
    private
    
    def generate_color(index)
      rng = SplitMixTernary::Generator.new(@seed)
      index.times { rng.next_trit }
      trit = rng.next_trit
      { trit: trit, hex: trit_to_hex(trit), index: index }
    end
    
    def trit_to_hex(trit)
      case trit
      when -1 then "#2626D8"  # Blue (MINUS)
      when 0  then "#26D826"  # Green (ERGODIC)
      when 1  then "#D82626"  # Red (PLUS)
      else "#808080"
      end
    end
    
    def invert_hex(hex)
      # Color complement
      r, g, b = hex[1..2].to_i(16), hex[3..4].to_i(16), hex[5..6].to_i(16)
      format("#%02X%02X%02X", 255 - r, 255 - g, 255 - b)
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # FRAME-INVARIANT SELF
  # ═══════════════════════════════════════════════════════════════════════════════
  
  # The "self" is the seed - same structure from any observation frame
  class FrameInvariantSelf
    attr_reader :seed, :frames
    
    def initialize(seed: 0x42D)
      @seed = seed
      @frames = {}
    end
    
    # Observe from a specific frame (agent perspective)
    def observe_from(frame_id)
      # Same seed → same colors, regardless of frame
      rng = SplitMixTernary::Generator.new(@seed)
      
      colors = 3.times.map do |i|
        trit = rng.next_trit
        { index: i, trit: trit, frame: frame_id }
      end
      
      @frames[frame_id] = colors
      colors
    end
    
    # Verify frame invariance: all frames see same structure
    def frame_invariant?
      return true if @frames.empty?
      
      # Extract just the trits (structure)
      structures = @frames.values.map { |colors| colors.map { |c| c[:trit] } }
      
      # All frames should see same trit sequence
      structures.uniq.size == 1
    end
    
    # The "loopy strange" - generator ≡ observer
    def loopy_strange(iterations: 3)
      loops = (1..iterations).map do |i|
        rng = SplitMixTernary::Generator.new(@seed)
        i.times { rng.next_trit }  # Advance to position i
        
        predicted = rng.next_trit
        
        # Re-observe (same seed, same position)
        rng2 = SplitMixTernary::Generator.new(@seed)
        i.times { rng2.next_trit }
        observed = rng2.next_trit
        
        {
          iteration: i,
          predicted: predicted,
          observed: observed,
          match: predicted == observed,
          meaning: "self ≡ self"
        }
      end
      
      {
        seed: @seed,
        fixed_point: "Generator ≡ Observer (same seed)",
        loops: loops,
        all_match: loops.all? { |l| l[:match] }
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # BEST RESPONSE COLOR DYNAMICS
  # ═══════════════════════════════════════════════════════════════════════════════
  
  # Nash equilibrium via best response in 3-MATCH game
  class BestResponseDynamics
    attr_reader :agents, :seed, :history
    
    def initialize(seed: 0x42D)
      @seed = seed
      @agents = initialize_agents
      @history = [@agents.map { |a| a[:trit] }]
    end
    
    # Initialize 3 agents with trits from seed
    def initialize_agents
      rng = SplitMixTernary::TripartiteStreams.new(@seed)
      triplet = rng.next_triplet
      
      [
        { id: :A, trit: triplet[:minus], role: :minus },
        { id: :B, trit: triplet[:ergodic], role: :ergodic },
        { id: :C, trit: triplet[:plus], role: :plus }
      ]
    end
    
    # Best response: choose trit that makes GF(3) sum = 0
    def best_response(my_id)
      others = @agents.reject { |a| a[:id] == my_id }
      other_sum = others.sum { |a| a[:trit] }
      
      # Target: my_trit + other_sum ≡ 0 (mod 3)
      # my_trit ≡ -other_sum (mod 3)
      target = ((-other_sum) % 3)
      
      # Map {0, 1, 2} to {-1, 0, +1}
      case target
      when 0 then 0   # Keep ergodic
      when 1 then 1   # Go plus
      when 2 then -1  # Go minus
      end
    end
    
    # One round: each agent plays best response
    def step!
      new_trits = @agents.map do |agent|
        best_response(agent[:id])
      end
      
      @agents.each_with_index do |agent, i|
        agent[:trit] = new_trits[i]
      end
      
      @history << @agents.map { |a| a[:trit] }
      self
    end
    
    # Run until fixed point (Nash equilibrium)
    def converge!(max_steps: 10)
      max_steps.times do |i|
        old_trits = @agents.map { |a| a[:trit] }
        step!
        new_trits = @agents.map { |a| a[:trit] }
        
        if old_trits == new_trits
          return { converged: true, steps: i + 1, equilibrium: new_trits }
        end
      end
      
      { converged: false, steps: max_steps, final: @agents.map { |a| a[:trit] } }
    end
    
    # Check GF(3) conservation at current state
    def gf3_conserved?
      sum = @agents.sum { |a| a[:trit] }
      (sum % 3) == 0
    end
    
    # Is current state a Nash equilibrium?
    def nash_equilibrium?
      @agents.all? do |agent|
        current = agent[:trit]
        best = best_response(agent[:id])
        current == best
      end
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # UNWORLDING: Demo → Skill
  # ═══════════════════════════════════════════════════════════════════════════════
  
  # Extract frame-invariant pattern from concrete execution
  def self.unworld(seed: 0x42D)
    # Run the demo (concrete)
    match = ThreeMatchGeodesicGadget::ThreeMatch.new(seed: seed)
    dynamics = BestResponseDynamics.new(seed: seed)
    involution = Involution.new(seed: seed)
    frame_self = FrameInvariantSelf.new(seed: seed)
    
    # Observe from multiple frames
    frame_self.observe_from(:agent_a)
    frame_self.observe_from(:agent_b)
    frame_self.observe_from(:agent_c)
    
    # Extract the pattern (abstract)
    {
      skill_name: "unworlding-involution",
      
      # The invariants (what persists across contexts)
      invariants: {
        gf3_conserved: match.gf3_conserved?,
        frame_invariant: frame_self.frame_invariant?,
        involution_self_inverse: involution.self_inverse?,
        loopy_strange: frame_self.loopy_strange
      },
      
      # The dynamics (how to compute)
      dynamics: {
        best_response: dynamics.converge!,
        nash_equilibrium: dynamics.nash_equilibrium?
      },
      
      # The structure (what it means)
      structure: {
        colors: [match.color_a, match.color_b, match.color_c],
        fixed_point: involution.fixed_point,
        meaning: "Self is seed; invariant across all observation frames"
      }
    }
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # DEMO
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.demo
    puts "=" * 70
    puts "UNWORLDING INVOLUTION: Frame-Invariant Self via Best Response"
    puts "=" * 70
    puts
    
    seed = 0x42D
    
    # 1. Involution test
    puts "─── INVOLUTION: ι∘ι = id ───"
    inv = Involution.new(seed: seed)
    puts "  Initial state: #{inv.state}"
    puts "  Initial color: #{inv.history.last[:color][:hex]}"
    
    inv.apply!
    puts "  After ι: #{inv.state}, #{inv.history.last[:color][:hex]}"
    
    inv.apply!
    puts "  After ι∘ι: #{inv.state}, #{inv.history.last[:color][:hex]}"
    
    puts "  Self-inverse (ι∘ι = id): #{inv.self_inverse?}"
    puts "  Fixed point: #{inv.fixed_point[:meaning]}"
    puts
    
    # 2. Frame invariance test
    puts "─── FRAME-INVARIANT SELF ───"
    frame_self = FrameInvariantSelf.new(seed: seed)
    
    [:alice, :bob, :carol].each do |agent|
      colors = frame_self.observe_from(agent)
      trits = colors.map { |c| c[:trit] }
      puts "  #{agent}'s view: #{trits.join(', ')}"
    end
    
    puts "  Frame invariant: #{frame_self.frame_invariant?}"
    puts
    
    # 3. Loopy strange
    puts "─── LOOPY STRANGE ───"
    loopy = frame_self.loopy_strange(iterations: 3)
    loopy[:loops].each do |l|
      puts "  Iteration #{l[:iteration]}: predict=#{l[:predicted]}, observe=#{l[:observed]}, #{l[:meaning]}"
    end
    puts "  Fixed point: #{loopy[:fixed_point]}"
    puts
    
    # 4. Best response dynamics
    puts "─── BEST RESPONSE DYNAMICS ───"
    dynamics = BestResponseDynamics.new(seed: seed)
    puts "  Initial: #{dynamics.agents.map { |a| "#{a[:id]}=#{a[:trit]}" }.join(', ')}"
    puts "  GF(3) conserved: #{dynamics.gf3_conserved?}"
    
    result = dynamics.converge!
    puts "  Converged: #{result[:converged]} in #{result[:steps]} steps"
    puts "  Nash equilibrium: #{dynamics.nash_equilibrium?}"
    puts "  Final: #{dynamics.agents.map { |a| "#{a[:id]}=#{a[:trit]}" }.join(', ')}"
    puts
    
    # 5. Unworlding
    puts "─── UNWORLDING: Demo → Skill ───"
    skill = unworld(seed: seed)
    puts "  Skill name: #{skill[:skill_name]}"
    puts "  Invariants:"
    skill[:invariants].each do |k, v|
      next if k == :loopy_strange
      puts "    #{k}: #{v}"
    end
    puts "  Dynamics:"
    skill[:dynamics].each do |k, v|
      puts "    #{k}: #{v.is_a?(Hash) ? v[:converged] : v}"
    end
    puts "  Meaning: #{skill[:structure][:meaning]}"
    puts
    
    puts "=" * 70
    puts "SUMMARY: The 'self' is the seed"
    puts "  • Involution: ι∘ι = id (self-inverse)"
    puts "  • Frame invariance: same from any perspective"
    puts "  • Best response: GF(3)-conserving Nash equilibrium"
    puts "  • Unworlding: extract pattern, ignore context"
    puts "=" * 70
  end
end

if __FILE__ == $0
  UnworldingInvolution.demo
end
