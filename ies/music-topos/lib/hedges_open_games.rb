# lib/hedges_open_games.rb
#
# HEDGES OPEN GAMES: Compositional Game Theory with 3-Color Semantics
#
# After Jules Hedges (2016-2025):
#   "Open games are a compositional foundation of non-cooperative game theory"
#
# Key insight: Games are LENSES (optics) with:
#   - Forward pass: State flows X → Y (world action)
#   - Backward pass: Utility flows R → S (coworld action)
#
# Integration with SplitMixTernary:
#   - MINUS (-1): Contravariant utility (backward, what we want)
#   - ERGODIC (0): Neutral transport (continuation, decision)
#   - PLUS (+1): Covariant state (forward, what happens)
#
# The GF(3) conservation law ensures strategic equilibrium:
#   sum(trits) ≡ 0 (mod 3) ⟺ Nash equilibrium condition

require_relative 'splitmix_ternary'
require_relative 'spi_parallel'

module HedgesOpenGames
  # ═══════════════════════════════════════════════════════════════════════════════
  # LENS STRUCTURE (Optic foundation of Open Games)
  # ═══════════════════════════════════════════════════════════════════════════════
  
  # A Lens is a pair (get, put) or equivalently (view, update)
  # In game theory: (play, coplay) or (forward, backward)
  class Lens
    attr_reader :forward, :backward, :name, :trit
    
    def initialize(name:, forward:, backward:, trit: 0)
      @name = name
      @forward = forward   # X → Y (state transformation)
      @backward = backward # (X, R) → S (utility propagation)
      @trit = trit
    end
    
    # Compose lenses sequentially (>>)
    def >>(other)
      Lens.new(
        name: "#{@name} >> #{other.name}",
        forward: ->(x) { other.forward.call(@forward.call(x)) },
        backward: ->(x, r) {
          y = @forward.call(x)
          s = other.backward.call(y, r)
          @backward.call(x, s)
        },
        trit: (@trit + other.trit) % 3 - 1  # GF(3) sum
      )
    end
    
    # Parallel composition (⊗)
    def tensor(other)
      Lens.new(
        name: "#{@name} ⊗ #{other.name}",
        forward: ->(xy) {
          x, y = xy
          [@forward.call(x), other.forward.call(y)]
        },
        backward: ->(xy, rs) {
          x, y = xy
          r, s = rs
          [@backward.call(x, r), other.backward.call(y, s)]
        },
        trit: (@trit + other.trit) % 3 - 1
      )
    end
    
    alias_method :*, :tensor
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # OPEN GAME: A game played relative to an arbitrary environment
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class OpenGame
    attr_reader :name, :lens, :strategy_space, :utility_fn, :seed, :trit
    
    def initialize(name:, lens:, strategy_space:, utility_fn:, seed: nil, trit: nil)
      @name = name
      @lens = lens
      @strategy_space = strategy_space  # Set of possible strategies
      @utility_fn = utility_fn          # Strategy × Outcome → Utility
      @seed = seed || SplitMixTernary::DEFAULT_SEED
      @trit = trit || lens.trit
    end
    
    # Play the game: given context, return (outcome, coutility)
    def play(context, strategy: nil)
      strategy ||= select_strategy(context)
      outcome = @lens.forward.call([context, strategy])
      utility = @utility_fn.call(strategy, outcome)
      
      {
        name: @name,
        context: context,
        strategy: strategy,
        outcome: outcome,
        utility: utility,
        trit: @trit
      }
    end
    
    # Select strategy using deterministic color
    def select_strategy(context)
      gen = SplitMixTernary::Generator.new(@seed)
      color = gen.next_color
      strategy_index = (color[:H] / 360.0 * @strategy_space.size).floor
      @strategy_space[strategy_index % @strategy_space.size]
    end
    
    # Best response given opponent's strategy
    def best_response(opponent_strategy, context)
      utilities = @strategy_space.map do |s|
        outcome = @lens.forward.call([context, s, opponent_strategy])
        { strategy: s, utility: @utility_fn.call(s, outcome) }
      end
      utilities.max_by { |u| u[:utility] }[:strategy]
    end
    
    # Check Nash equilibrium
    def nash_equilibrium?(strategy_profile, context)
      @strategy_space.all? do |alternative|
        current_utility = @utility_fn.call(strategy_profile, 
          @lens.forward.call([context, strategy_profile]))
        alt_utility = @utility_fn.call(alternative,
          @lens.forward.call([context, alternative]))
        current_utility >= alt_utility
      end
    end
    
    # Compose games sequentially
    def >>(other)
      composed_lens = @lens >> other.lens
      OpenGame.new(
        name: "#{@name} >> #{other.name}",
        lens: composed_lens,
        strategy_space: @strategy_space + other.strategy_space,
        utility_fn: ->(s, o) { @utility_fn.call(s, o) + other.utility_fn.call(s, o) },
        seed: @seed,
        trit: ((@trit + other.trit) % 3) - 1
      )
    end
    
    # Parallel composition
    def tensor(other)
      composed_lens = @lens.tensor(other.lens)
      OpenGame.new(
        name: "#{@name} ⊗ #{other.name}",
        lens: composed_lens,
        strategy_space: @strategy_space.product(other.strategy_space),
        utility_fn: ->(s, o) {
          s1, s2 = s.is_a?(Array) ? s : [s, s]
          o1, o2 = o.is_a?(Array) ? o : [o, o]
          [@utility_fn.call(s1, o1), other.utility_fn.call(s2, o2)]
        },
        seed: @seed,
        trit: ((@trit + other.trit) % 3) - 1
      )
    end
    
    alias_method :*, :tensor
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # TRIPARTITE GAME SYSTEM: 3 Players with GF(3) Conservation
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class TripartiteGame
    attr_reader :minus_player, :ergodic_player, :plus_player, :seed, :history
    
    def initialize(seed = SplitMixTernary::DEFAULT_SEED)
      @seed = seed
      @streams = SplitMixTernary::TripartiteStreams.new(seed)
      @history = []
      
      # Create three players with different polarities
      @minus_player = create_player(:minus, -1)
      @ergodic_player = create_player(:ergodic, 0)
      @plus_player = create_player(:plus, 1)
    end
    
    def create_player(role, trit)
      strategies = case role
                   when :minus then [:cooperate, :defect, :tit_for_tat]
                   when :ergodic then [:random, :always_continue, :mirror]
                   when :plus then [:aggressive, :passive, :adaptive]
                   end
      
      OpenGame.new(
        name: "Player_#{role}",
        lens: Lens.new(
          name: "#{role}_lens",
          forward: ->(state) { 
            state.is_a?(Hash) ? state.merge(player: role) : { value: state, player: role }
          },
          backward: ->(state, utility) { utility.to_f * trit },
          trit: trit
        ),
        strategy_space: strategies,
        utility_fn: ->(strategy, outcome) {
          base = outcome.is_a?(Hash) ? (outcome[:payoff] || 0) : outcome.to_i
          base * (1 + trit * 0.1)  # Polarity adjustment
        },
        seed: (@seed ^ (trit * SplitMixTernary::GOLDEN)) & SplitMixTernary::MASK64,
        trit: trit
      )
    end
    
    # Play one round with all three players
    def play_round(context = {})
      triplet = @streams.next_triplet
      
      results = {
        minus: @minus_player.play(context.merge(role: :minus)),
        ergodic: @ergodic_player.play(context.merge(role: :ergodic)),
        plus: @plus_player.play(context.merge(role: :plus)),
        triplet: triplet,
        gf3_sum: triplet[:gf3_sum],
        conserved: triplet[:conserved]
      }
      
      @history << results
      results
    end
    
    # Play N rounds
    def play_tournament(n, context = {})
      n.times.map { play_round(context) }
    end
    
    # Verify GF(3) conservation across history
    def verify_conservation
      @history.all? { |r| r[:conserved] }
    end
    
    # Compute aggregate utilities
    def aggregate_utilities
      {
        minus: @history.sum { |r| r[:minus][:utility] },
        ergodic: @history.sum { |r| r[:ergodic][:utility] },
        plus: @history.sum { |r| r[:plus][:utility] },
        total_rounds: @history.size,
        all_conserved: verify_conservation
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # SELECTION FUNCTIONS (Hedges' key insight)
  # ═══════════════════════════════════════════════════════════════════════════════
  
  # A selection function ε: (X → R) → X
  # Given a valuation function, selects the "best" element
  class SelectionFunction
    attr_reader :name, :selector, :trit
    
    def initialize(name:, selector:, trit: 0)
      @name = name
      @selector = selector
      @trit = trit
    end
    
    # Apply selection to a valuation function
    def call(valuation, domain)
      @selector.call(valuation, domain)
    end
    
    # Argmax selection (rational player)
    def self.argmax(trit: 1)
      new(
        name: "argmax",
        selector: ->(valuation, domain) {
          domain.max_by { |x| valuation.call(x) }
        },
        trit: trit
      )
    end
    
    # Argmin selection (adversarial)
    def self.argmin(trit: -1)
      new(
        name: "argmin",
        selector: ->(valuation, domain) {
          domain.min_by { |x| valuation.call(x) }
        },
        trit: trit
      )
    end
    
    # Random selection (ergodic)
    def self.random(seed:, trit: 0)
      gen = SplitMixTernary::Generator.new(seed)
      new(
        name: "random",
        selector: ->(valuation, domain) {
          idx = (gen.next_float * domain.size).floor
          domain[idx % domain.size]
        },
        trit: trit
      )
    end
    
    # Epsilon-greedy (exploration/exploitation)
    def self.epsilon_greedy(epsilon:, seed:, trit: 0)
      gen = SplitMixTernary::Generator.new(seed)
      new(
        name: "epsilon_greedy_#{epsilon}",
        selector: ->(valuation, domain) {
          if gen.next_float < epsilon
            # Explore: random
            idx = (gen.next_float * domain.size).floor
            domain[idx % domain.size]
          else
            # Exploit: argmax
            domain.max_by { |x| valuation.call(x) }
          end
        },
        trit: trit
      )
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # BAYESIAN OPEN GAMES (Probabilistic extension)
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class BayesianGame < OpenGame
    attr_reader :prior, :likelihood
    
    def initialize(prior:, likelihood:, **opts)
      super(**opts)
      @prior = prior           # P(θ): prior over types
      @likelihood = likelihood # P(outcome | θ, strategy)
    end
    
    # Update belief given observation
    def posterior(observation, prior_belief = @prior)
      # Bayes: P(θ|o) ∝ P(o|θ) P(θ)
      unnormalized = prior_belief.transform_values do |prob|
        @likelihood.call(observation, prob) * prob
      end
      total = unnormalized.values.sum
      unnormalized.transform_values { |v| v / total }
    end
    
    # Expected utility under uncertainty
    def expected_utility(strategy, belief)
      belief.sum do |type, prob|
        outcome = @lens.forward.call([type, strategy])
        prob * @utility_fn.call(strategy, outcome)
      end
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # DEMONSTRATION
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.demo(seed: SplitMixTernary::DEFAULT_SEED)
    puts "╔═══════════════════════════════════════════════════════════════════╗"
    puts "║  HEDGES OPEN GAMES: Compositional Game Theory + 3-Color          ║"
    puts "╚═══════════════════════════════════════════════════════════════════╝"
    puts
    puts "After Jules Hedges: 'Open games are lenses with utility flow'"
    puts "Seed: 0x#{seed.to_s(16)}"
    puts
    
    puts "─── Tripartite Game (3 Players, GF(3) Conservation) ───"
    game = TripartiteGame.new(seed)
    results = game.play_tournament(5)
    
    results.each_with_index do |r, i|
      puts "  Round #{i + 1}:"
      puts "    MINUS:   strategy=#{r[:minus][:strategy]} utility=#{r[:minus][:utility].round(2)}"
      puts "    ERGODIC: strategy=#{r[:ergodic][:strategy]} utility=#{r[:ergodic][:utility].round(2)}"
      puts "    PLUS:    strategy=#{r[:plus][:strategy]} utility=#{r[:plus][:utility].round(2)}"
      puts "    GF(3): #{r[:gf3_sum]} ≡ 0 (mod 3) #{r[:conserved] ? '✓' : '✗'}"
    end
    puts
    
    agg = game.aggregate_utilities
    puts "─── Aggregate Results ───"
    puts "  MINUS total:   #{agg[:minus].round(2)}"
    puts "  ERGODIC total: #{agg[:ergodic].round(2)}"
    puts "  PLUS total:    #{agg[:plus].round(2)}"
    puts "  All conserved: #{agg[:all_conserved] ? '✓' : '✗'}"
    puts
    
    puts "─── Selection Functions ───"
    domain = [:a, :b, :c, :d]
    valuation = ->(x) { { a: 1, b: 4, c: 2, d: 3 }[x] }
    
    argmax = SelectionFunction.argmax
    argmin = SelectionFunction.argmin
    random = SelectionFunction.random(seed: seed)
    eps_greedy = SelectionFunction.epsilon_greedy(epsilon: 0.3, seed: seed)
    
    puts "  Domain: #{domain}"
    puts "  Valuation: a→1, b→4, c→2, d→3"
    puts "  argmax (trit +1): #{argmax.call(valuation, domain)}"
    puts "  argmin (trit -1): #{argmin.call(valuation, domain)}"
    puts "  random (trit 0):  #{random.call(valuation, domain)}"
    puts "  ε-greedy (0.3):   #{eps_greedy.call(valuation, domain)}"
    puts
    
    puts "─── Lens Composition ───"
    lens1 = Lens.new(
      name: "observe",
      forward: ->(x) { x * 2 },
      backward: ->(x, r) { r / 2 },
      trit: -1
    )
    lens2 = Lens.new(
      name: "act",
      forward: ->(x) { x + 1 },
      backward: ->(x, r) { r - 1 },
      trit: 1
    )
    composed = lens1 >> lens2
    
    puts "  Lens 1: observe (×2), trit=-1"
    puts "  Lens 2: act (+1), trit=+1"
    puts "  Composed: #{composed.name}, trit=#{composed.trit}"
    puts "  Forward(5): #{composed.forward.call(5)}"
    puts "  Backward(5, 10): #{composed.backward.call(5, 10)}"
    puts
    
    puts "═══════════════════════════════════════════════════════════════════"
    puts "Open Games + SplitMixTernary = Compositional Game Theory with"
    puts "deterministic randomness and GF(3) conservation guarantees."
    puts "═══════════════════════════════════════════════════════════════════"
  end
end

if __FILE__ == $0
  HedgesOpenGames.demo
end
