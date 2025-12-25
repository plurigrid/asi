# frozen_string_literal: true

# SynergyMarket: Prediction Markets on Capability Synergy
#
# Extends ColorCapability + InteractomeOpenGames to enable betting on:
# - Synergy of capability combinations (coverage, composition, novelty)
# - Expert triad collaborations and their emergent properties
# - GF(3)-balanced settlement across synergy outcomes
#
# Key insight: Synergy IS measurable and unforgeable via:
#   1. Coverage: portion of capability lattice reached
#   2. Composition: how well capabilities chain (play → coplay)
#   3. Unused potential: unexplored combinations from partial set
#   4. Novelty: compression progress of synergy outcome
#
# References:
#   - Hedges (2016): Compositional Game Theory
#   - Schmidhuber: Compression Progress as Intrinsic Curiosity
#   - ACSet formalism: Patterson 2021

require_relative 'color_capability'
require_relative 'interactome_open_games'
require_relative 'splitmix_ternary'

module MusicTopos
  module SynergyMarket
    # =========================================================================
    # CAPABILITY SYNERGY: Measure how well capabilities combine
    # =========================================================================

    class CapabilitySynergy
      attr_reader :capabilities, :seed, :index, :triad, :metrics

      def initialize(capabilities:, seed:, index:, triad: nil)
        @capabilities = capabilities  # Array of Capability or ExpertPlayer objects
        @seed = seed
        @index = index
        @triad = triad  # Optional: the triadic composition
        @metrics = compute_metrics
      end

      # Coverage: what portion of the capability lattice is reached?
      # Higher coverage = more comprehensive collaboration
      def coverage
        @metrics[:coverage]
      end

      # Composition: how well do capabilities chain together?
      # Measured by play → coplay alignment across the chain
      def composition_quality
        @metrics[:composition]
      end

      # Unused Potential: what unexplored combinations remain?
      # If using 2 of 3 experts, unused potential = 1
      def unused_potential
        @metrics[:unused_potential]
      end

      # Novelty: how surprising is this synergy?
      # Based on compression progress of the combined color
      def novelty
        @metrics[:novelty]
      end

      # Synergy Score: overall quality of this combination
      # Weighted combination of metrics
      def synergy_score
        @metrics[:score]
      end

      # Deterministic color for this synergy
      def synergy_color
        @metrics[:color]
      end

      private

      def compute_metrics
        coverage = compute_coverage
        composition = compute_composition
        unused = compute_unused_potential
        novelty = compute_novelty

        # Weighted synergy score
        # Prefer: coverage > unused potential > composition > novelty
        score = (coverage * 0.4) +
                ((1.0 - unused) * 0.3) +  # Inverse: using all is better
                (composition * 0.2) +
                (novelty * 0.1)

        {
          coverage: coverage,
          composition: composition,
          unused_potential: unused,
          novelty: novelty,
          score: score,
          color: derive_synergy_color
        }
      end

      def compute_coverage
        # Coverage = portion of all possible triad compositions this represents
        # Max coverage = all 3 experts (triad) = 1.0
        # Coverage = capabilities.size / 3.0
        [@capabilities.size / 3.0, 1.0].min
      end

      def compute_composition
        # Composition quality = how well play outputs align with coplay inputs
        # Perfect composition = all intermediate outputs are valid next inputs
        return 1.0 if @capabilities.size <= 1

        alignments = []
        @capabilities.each_cons(2) do |cap1, cap2|
          # Check type alignment between cap1's output and cap2's input
          # Simplified: check trit balance
          output_trit = trit_of(cap1)
          input_trit = trit_of(cap2)

          # Good alignment if trits form a sequence -1 → 0 → +1
          alignment = case [output_trit, input_trit]
                      when [-1, 0], [0, +1], [-1, +1] then 1.0
                      when [0, -1], [+1, 0], [+1, -1] then 0.5
                      else 0.0
                      end
          alignments << alignment
        end

        alignments.empty? ? 1.0 : alignments.sum / alignments.size
      end

      def compute_unused_potential
        # Unused potential = how many possible compositions could we still explore?
        # For triadic system: max = 3!, min = 1 (singleton)
        total_possible = [6, 2, 1, 0][@capabilities.size] || 0  # factorial approximation
        used = 1  # This combination counts as "used"

        if total_possible.zero?
          0.0
        else
          (total_possible - used) / total_possible.to_f
        end
      end

      def compute_novelty
        # Novelty = compression progress of synergy outcome
        # Higher entropy = more surprising = higher novelty
        hex_color = derive_synergy_color
        digits = hex_color[1..6].chars.map { |c| c.to_i(16) }
        variance = digits.map { |d| (d - digits.sum / 6.0) ** 2 }.sum / 6.0

        # Normalize to [0, 1]
        Math.sqrt(variance) / 16.0
      end

      def derive_synergy_color
        # Deterministic color from seed + synergy of capabilities
        generator = SplitMixTernary::Generator.new(@seed)
        @index.times { generator.next_trit }

        # Additional iterations for each capability in the synergy
        @capabilities.each { |_cap| generator.next_trit }

        generator.next_color[:hex]
      end

      def trit_of(capability)
        case capability
        when ColorCapability::Capability
          capability.issuer_trit
        when InteractomeOpenGames::ExpertPlayer
          capability.trit
        else
          0  # Default: coordinator
        end
      end
    end

    # =========================================================================
    # SYNERGY LATTICE: Poset of capability combinations
    # =========================================================================

    class SynergyLattice
      attr_reader :elements, :order_relation

      def initialize(capability_pool)
        @capability_pool = capability_pool
        @elements = build_lattice
        @order_relation = build_partial_order
      end

      # Generate all non-empty subsets of the capability pool
      def build_lattice
        pool_size = @capability_pool.size
        (1..pool_size).flat_map do |r|
          @capability_pool.combination(r).to_a
        end
      end

      # Partial order: A ≤ B if A ⊆ B (subset relation)
      def build_partial_order
        Hash.new { |h, k| h[k] = [] }.tap do |po|
          @elements.each do |a|
            @elements.each do |b|
              if (a & b) == a && a != b  # A is strict subset of B
                po[a] << b
              end
            end
          end
        end
      end

      # Find upper bounds (synergies that contain both A and B)
      def least_upper_bound(a, b)
        (a + b).uniq  # Union of both sets
      end

      # Find lower bounds (subsets common to both A and B)
      def greatest_lower_bound(a, b)
        a & b  # Intersection of both sets
      end

      def cover_relation(a)
        # Elements immediately above a in the lattice (covers a)
        @order_relation[a]
      end
    end

    # =========================================================================
    # SYNERGY BET: Prediction market for synergy outcomes
    # =========================================================================

    class SynergyBet
      attr_reader :proposer_trit, :synergy, :predicted_score, :stake, :timestamp

      def initialize(
        proposer_trit:,
        synergy:,
        predicted_score:,
        stake: 1.0
      )
        @proposer_trit = proposer_trit
        @synergy = synergy
        @predicted_score = predicted_score
        @stake = stake
        @timestamp = Time.now
      end

      def to_h
        {
          proposer_trit: @proposer_trit,
          capabilities: @synergy.capabilities.map(&:name),
          seed: @synergy.seed,
          index: @synergy.index,
          predicted_score: @predicted_score,
          stake: @stake,
          timestamp: @timestamp
        }
      end
    end

    # =========================================================================
    # SYNERGY PREDICTION MARKET: Full market mechanics
    # =========================================================================

    class SynergyPredictionMarket
      attr_reader :swarm, :lattice, :bets, :resolved

      def initialize(swarm, capability_pool = nil)
        @swarm = swarm
        @capability_pool = capability_pool || default_capability_pool
        @lattice = SynergyLattice.new(@capability_pool)
        @bets = []
        @resolved = []
      end

      # Agent-O-Rama (+1) proposes a synergy bet
      def propose_synergy_bet(
        capabilities:,
        seed: 1069,
        index: 1,
        predicted_score: nil,
        stake: 1.0
      )
        synergy = CapabilitySynergy.new(
          capabilities: capabilities,
          seed: seed,
          index: index
        )

        # If no prediction given, use actual synergy score + small noise
        predicted = predicted_score || synergy.synergy_score

        bet = SynergyBet.new(
          proposer_trit: +1,
          synergy: synergy,
          predicted_score: predicted,
          stake: stake
        )

        @bets << bet
        bet
      end

      # Shadow Goblin (-1) scores the synergy bet
      def score_synergy_bet(bet)
        actual_score = bet.synergy.synergy_score

        # Prediction error
        error = (bet.predicted_score - actual_score).abs
        correct = error < 0.1  # Within 10% is considered "correct"

        # Compression progress from synergy novelty
        delta_c = correct ? bet.synergy.novelty * bet.synergy.composition_quality : -bet.stake

        {
          bet: bet,
          actual_synergy_score: actual_score,
          actual_color: bet.synergy.synergy_color,
          error: error,
          correct: correct,
          compression_delta: delta_c,
          metrics: {
            coverage: bet.synergy.coverage,
            composition: bet.synergy.composition_quality,
            unused_potential: bet.synergy.unused_potential,
            novelty: bet.synergy.novelty
          },
          scored_by: -1
        }
      end

      # Coordinator (0) settles the synergy bet
      def settle_synergy_bet(scored)
        payout = scored[:correct] ? scored[:bet].stake * (1 + scored[:compression_delta]) : 0

        settlement = {
          bet: scored[:bet],
          score: scored,
          payout: payout,
          settled_by: 0,
          settled_at: Time.now,
          gf3_flow: "#{scored[:bet].proposer_trit} → #{scored[:scored_by]} → 0"
        }

        @resolved << settlement
        settlement
      end

      # Market summary
      def market_stats
        {
          total_bets: @bets.size,
          resolved_bets: @resolved.size,
          total_stakes: @bets.sum(&:stake),
          total_payouts: @resolved.sum { |r| r[:payout] },
          lattice_size: @lattice.elements.size,
          gf3_sum: [@swarm.shadow.trit, @swarm.coordinator.trit, @swarm.agent_o_rama.trit].sum
        }
      end

      private

      def default_capability_pool
        # Use experts from InteractomeOpenGames if available
        [
          InteractomeOpenGames::Experts::HEDGES,
          InteractomeOpenGames::Experts::BAEZ,
          InteractomeOpenGames::Experts::GENOVESE
        ]
      end
    end

    # =========================================================================
    # DEMO: Synergy Market in Action
    # =========================================================================

    def self.demo_synergy_market
      puts "=== Synergy Prediction Market Demo ==="

      # Create swarm
      swarm = ColorCapability::GoblinSwarm.new(genesis_seed: 1069)

      # Create market
      market = SynergyPredictionMarket.new(swarm)

      # Propose a synergy bet: all three experts together
      capabilities = [
        InteractomeOpenGames::Experts::HEDGES,
        InteractomeOpenGames::Experts::BAEZ,
        InteractomeOpenGames::Experts::GENOVESE
      ]

      puts "\n--- Proposing Synergy Bet ---"
      bet = market.propose_synergy_bet(
        capabilities: capabilities,
        seed: 1069,
        index: 10,
        predicted_score: 0.8,
        stake: 50.0
      )

      synergy = bet.synergy
      puts "Synergy: #{capabilities.map(&:name).join(' ⊗ ')}"
      puts "  Coverage: #{synergy.coverage.round(3)}"
      puts "  Composition: #{synergy.composition_quality.round(3)}"
      puts "  Unused Potential: #{synergy.unused_potential.round(3)}"
      puts "  Novelty: #{synergy.novelty.round(3)}"
      puts "  Color: #{synergy.synergy_color}"
      puts "  Score: #{synergy.synergy_score.round(3)}"

      # Shadow Goblin scores
      puts "\n--- Shadow Goblin Scores ---"
      scored = market.score_synergy_bet(bet)
      puts "Prediction Error: #{scored[:error].round(3)}"
      puts "Correct: #{scored[:correct]}"
      puts "ΔC: #{scored[:compression_delta].round(4)}"

      # Coordinator settles
      puts "\n--- Coordinator Settles ---"
      settlement = market.settle_synergy_bet(scored)
      puts "Payout: #{settlement[:payout].round(2)}"
      puts "GF(3) Flow: #{settlement[:gf3_flow]}"

      # Market stats
      puts "\n--- Market Statistics ---"
      stats = market.market_stats
      stats.each { |k, v| puts "#{k}: #{v}" }
    end

    # Demo: Synergy Lattice Exploration
    def self.demo_synergy_lattice
      puts "\n=== Synergy Lattice Exploration ==="

      capabilities = [
        InteractomeOpenGames::Experts::HEDGES,
        InteractomeOpenGames::Experts::BAEZ,
        InteractomeOpenGames::Experts::GENOVESE
      ]

      lattice = SynergyLattice.new(capabilities)

      puts "\nAll possible synergies (elements in lattice):"
      lattice.elements.each_with_index do |element, i|
        names = element.map(&:name).join(" ⊗ ")
        puts "  #{i + 1}. #{names}"
      end

      # Show partial order
      puts "\nPartial order (coverage hierarchy):"
      lattice.elements.sort_by(&:size).each do |a|
        covers = lattice.cover_relation(a)
        unless covers.empty?
          from = a.map(&:name).join(" ⊗ ")
          to = covers.first.map(&:name).join(" ⊗ ") if covers.any?
          puts "  #{from} ≤ #{to}"
        end
      end
    end
  end
end

# Run demo if executed directly
if __FILE__ == $0
  MusicTopos::SynergyMarket.demo_synergy_lattice
  MusicTopos::SynergyMarket.demo_synergy_market
end
