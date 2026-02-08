# frozen_string_literal: true

# Interactome Open Games: Expert Triads as Compositional Games
#
# Models individuals from IES interactome as players in open games,
# with play/coplay composition and GF(3) balanced dynamics.
#
# Reference: Hedges, "Compositional Game Theory" (2016)
#            Ghani et al., "Compositional Game Theory" (2018)

module MusicTopos
  module InteractomeOpenGames
    # Open Game morphism in symmetric monoidal category
    #
    #         ┌───────────┐
    #    X ──→│  Player   │──→ Y
    #         │           │
    #    R ←──│           │←── S
    #         └───────────┘
    #
    # - play:   X → Y  (forward strategy/knowledge)
    # - coplay: X × S → R  (backward utility/validation)
    #
    class OpenGame
      attr_reader :name, :trit, :play, :coplay, :domain, :codomain

      def initialize(name:, trit:, domain:, codomain:, play:, coplay:)
        @name = name
        @trit = trit  # -1 (validator), 0 (coordinator), +1 (generator)
        @domain = domain
        @codomain = codomain
        @play = play      # Proc: X → Y
        @coplay = coplay  # Proc: (X, S) → R
      end

      # Sequential composition: self ; other
      # (A ⊸ B) ; (B ⊸ C) = (A ⊸ C)
      def seq(other)
        raise "Domain mismatch: #{codomain} vs #{other.domain}" unless codomain == other.domain

        OpenGame.new(
          name: "#{name} ; #{other.name}",
          trit: (trit + other.trit) % 3 - 1,  # GF(3) addition
          domain: domain,
          codomain: other.codomain,
          play: ->(x) { other.play.call(play.call(x)) },
          coplay: ->(x, s) {
            y = play.call(x)
            r_other = other.coplay.call(y, s)
            coplay.call(x, r_other)
          }
        )
      end
      alias_method :>>, :seq

      # Parallel composition: self ⊗ other
      # (A ⊸ B) ⊗ (C ⊸ D) = (A × C ⊸ B × D)
      def par(other)
        OpenGame.new(
          name: "#{name} ⊗ #{other.name}",
          trit: (trit + other.trit) % 3 - 1,
          domain: [domain, other.domain],
          codomain: [codomain, other.codomain],
          play: ->((x1, x2)) { [play.call(x1), other.play.call(x2)] },
          coplay: ->((x1, x2), (s1, s2)) {
            [coplay.call(x1, s1), other.coplay.call(x2, s2)]
          }
        )
      end
      alias_method :*, :par

      # Check Nash equilibrium at state x with utility u
      def equilibrium?(x, utility)
        y = play.call(x)
        r = coplay.call(x, utility)
        # In equilibrium if no profitable deviation
        # (simplified: check if utility is maximized)
        r >= 0
      end

      def to_s
        "OpenGame(#{name}, trit=#{trit}, #{domain} ⊸ #{codomain})"
      end
    end

    # Expert Player: Individual from interactome as open game
    class ExpertPlayer < OpenGame
      attr_reader :expertise, :interaction_weight, :color

      TRIT_COLORS = {
        -1 => '#2626D8',  # Blue (validator)
         0 => '#26D826',  # Green (coordinator)
        +1 => '#D82626'   # Red (generator)
      }.freeze

      def initialize(name:, trit:, expertise:, interaction_weight: 1.0)
        @expertise = expertise
        @interaction_weight = interaction_weight
        @color = TRIT_COLORS[trit]

        super(
          name: name,
          trit: trit,
          domain: expertise_domain(trit),
          codomain: expertise_codomain(trit),
          play: build_play(expertise, trit),
          coplay: build_coplay(expertise, trit)
        )
      end

      private

      def expertise_domain(trit)
        case trit
        when -1 then :claims      # Validators receive claims to check
        when  0 then :knowledge   # Coordinators receive knowledge to bridge
        when +1 then :specs       # Generators receive specs to implement
        end
      end

      def expertise_codomain(trit)
        case trit
        when -1 then :proofs      # Validators produce proofs
        when  0 then :bridges     # Coordinators produce bridges
        when +1 then :artifacts   # Generators produce artifacts
        end
      end

      def build_play(expertise, trit)
        ->(input) {
          # Forward pass: transform input through expertise
          { 
            source: name,
            expertise: expertise,
            trit: trit,
            input: input,
            output: "#{expertise}(#{input})",
            weight: interaction_weight
          }
        }
      end

      def build_coplay(expertise, trit)
        ->(input, utility) {
          # Backward pass: propagate utility through expertise
          case trit
          when -1  # Validator: utility from correctness
            utility[:correctness] || 0
          when 0   # Coordinator: utility from bridge quality
            utility[:coherence] || 0
          when +1  # Generator: utility from novelty
            utility[:novelty] || 0
          end
        }
      end
    end

    # Triad: GF(3)-balanced group of three experts
    class Triad
      attr_reader :name, :validator, :coordinator, :generator, :game

      def initialize(name:, validator:, coordinator:, generator:)
        @name = name
        @validator = validator    # trit = -1
        @coordinator = coordinator # trit = 0
        @generator = generator    # trit = +1

        validate_gf3!
        @game = compose_triad
      end

      def gf3_sum
        validator.trit + coordinator.trit + generator.trit
      end

      def balanced?
        gf3_sum == 0
      end

      # Full triad game: validator ; coordinator ; generator
      def compose_triad
        (validator >> coordinator) >> generator
      end

      # Parallel composition with another triad
      def par(other)
        game * other.game
      end

      # Add player: returns new triad with player substituted
      def add_player(player, position:)
        case position
        when :validator
          Triad.new(name: "#{name}+#{player.name}", 
                   validator: player, 
                   coordinator: coordinator, 
                   generator: generator)
        when :coordinator
          Triad.new(name: "#{name}+#{player.name}",
                   validator: validator,
                   coordinator: player,
                   generator: generator)
        when :generator
          Triad.new(name: "#{name}+#{player.name}",
                   validator: validator,
                   coordinator: coordinator,
                   generator: player)
        end
      end

      # Remove player: returns degraded dyad (no longer GF(3) balanced)
      def remove_player(position:)
        case position
        when :validator
          Dyad.new(validator.name, coordinator, generator)
        when :coordinator
          Dyad.new(coordinator.name, validator, generator)
        when :generator
          Dyad.new(generator.name, validator, coordinator)
        end
      end

      def to_s
        "Triad(#{name}: #{validator.name}(-1) ⊗ #{coordinator.name}(0) ⊗ #{generator.name}(+1))"
      end

      private

      def validate_gf3!
        unless balanced?
          raise "GF(3) violation: #{validator.trit} + #{coordinator.trit} + #{generator.trit} = #{gf3_sum} ≠ 0"
        end
      end
    end

    # Dyad: Unbalanced pair (result of player removal)
    class Dyad
      attr_reader :removed_name, :player1, :player2, :imbalance

      def initialize(removed_name, player1, player2)
        @removed_name = removed_name
        @player1 = player1
        @player2 = player2
        @imbalance = player1.trit + player2.trit
      end

      def gf3_deficit
        (0 - imbalance) % 3 - 1  # What trit is needed to rebalance
      end

      def rebalance_with(player)
        if player.trit == gf3_deficit
          # Determine new positions
          players = [player1, player2, player].sort_by(&:trit)
          Triad.new(
            name: "Rebalanced(#{removed_name}→#{player.name})",
            validator: players.find { |p| p.trit == -1 },
            coordinator: players.find { |p| p.trit == 0 },
            generator: players.find { |p| p.trit == +1 }
          )
        else
          raise "Cannot rebalance: need trit=#{gf3_deficit}, got trit=#{player.trit}"
        end
      end

      def to_s
        "Dyad(missing #{removed_name}: #{player1.name}(#{player1.trit}) ⊗ #{player2.name}(#{player2.trit}), deficit=#{gf3_deficit})"
      end
    end

    # =========================================================================
    # IES INTERACTOME EXPERTS
    # =========================================================================

    module Experts
      # Triad 1: Categorical Game Theory
      HEDGES = ExpertPlayer.new(
        name: 'Jules Hedges',
        trit: -1,
        expertise: 'open-games',
        interaction_weight: 8401
      )

      BAEZ = ExpertPlayer.new(
        name: 'John Baez',
        trit: 0,
        expertise: 'physics-math',
        interaction_weight: 15128
      )

      GENOVESE = ExpertPlayer.new(
        name: 'Fabrizio Genovese',
        trit: +1,
        expertise: 'applied-crypto',
        interaction_weight: 12386
      )

      # Triad 2: Sheaf-Theoretic Intelligence
      EGOLF = ExpertPlayer.new(
        name: 'David Egolf',
        trit: -1,
        expertise: 'sheaf-theory',
        interaction_weight: 5000
      )

      SHULMAN = ExpertPlayer.new(
        name: 'Mike Shulman',
        trit: 0,
        expertise: 'HoTT',
        interaction_weight: 3000
      )

      SARAHZRF = ExpertPlayer.new(
        name: 'sarahzrf',
        trit: +1,
        expertise: 'applied-CT',
        interaction_weight: 2500
      )

      # Triad 3: Neural-Categorical Synthesis
      BETWEENNESS = ExpertPlayer.new(
        name: 'Betweenness',
        trit: -1,
        expertise: 'active-inference',
        interaction_weight: 1000
      )

      MANTISSA = ExpertPlayer.new(
        name: 'Mantissa',
        trit: 0,
        expertise: 'comonads',
        interaction_weight: 800
      )

      MODALNOAH = ExpertPlayer.new(
        name: 'ModalNoah',
        trit: +1,
        expertise: 'neural-category',
        interaction_weight: 600
      )

      # Triad 4: Open-Ended Evolution
      GWERN = ExpertPlayer.new(
        name: 'gwern',
        trit: -1,
        expertise: 'empirical-AI',
        interaction_weight: 500
      )

      CHRISHYPERNYM = ExpertPlayer.new(
        name: 'ChrisHypernym',
        trit: 0,
        expertise: 'LLM-extraction',
        interaction_weight: 300
      )

      ZASHIROVICI = ExpertPlayer.new(
        name: 'ZashiroVICI',
        trit: +1,
        expertise: 'future-systems',
        interaction_weight: 200
      )
    end

    # =========================================================================
    # TRIAD COMPOSITIONS
    # =========================================================================

    module Triads
      include Experts

      CGT = Triad.new(
        name: 'Categorical-Game-Theory',
        validator: HEDGES,
        coordinator: BAEZ,
        generator: GENOVESE
      )

      STI = Triad.new(
        name: 'Sheaf-Theoretic-Intelligence',
        validator: EGOLF,
        coordinator: SHULMAN,
        generator: SARAHZRF
      )

      NCS = Triad.new(
        name: 'Neural-Categorical-Synthesis',
        validator: BETWEENNESS,
        coordinator: MANTISSA,
        generator: MODALNOAH
      )

      OEE = Triad.new(
        name: 'Open-Ended-Evolution',
        validator: GWERN,
        coordinator: CHRISHYPERNYM,
        generator: ZASHIROVICI
      )

      ALL = [CGT, STI, NCS, OEE].freeze
    end

    # =========================================================================
    # COMPOSITION EXAMPLES
    # =========================================================================

    class << self
      # Demonstrate sequential composition within triad
      def demo_sequential_composition
        include Experts

        puts "=== Sequential Composition: Hedges ; Baez ; Genovese ==="
        
        # Step 1: Hedges validates
        hedges_out = HEDGES.play.call(:game_spec)
        puts "1. Hedges.play(:game_spec) → #{hedges_out[:output]}"
        
        # Step 2: Baez coordinates
        baez_out = BAEZ.play.call(hedges_out)
        puts "2. Baez.play(hedges_out) → #{baez_out[:output]}"
        
        # Step 3: Genovese generates
        genovese_out = GENOVESE.play.call(baez_out)
        puts "3. Genovese.play(baez_out) → #{genovese_out[:output]}"
        
        # Coplay backward
        puts "\n=== Coplay Backward ==="
        utility = { correctness: 0.9, coherence: 0.85, novelty: 0.95 }
        
        genovese_r = GENOVESE.coplay.call(baez_out, utility)
        puts "3. Genovese.coplay(utility) → #{genovese_r}"
        
        baez_r = BAEZ.coplay.call(hedges_out, utility)
        puts "2. Baez.coplay(utility) → #{baez_r}"
        
        hedges_r = HEDGES.coplay.call(:game_spec, utility)
        puts "1. Hedges.coplay(utility) → #{hedges_r}"
      end

      # Demonstrate parallel composition across triads
      def demo_parallel_composition
        include Triads

        puts "\n=== Parallel Composition: CGT ⊗ STI ==="
        
        parallel_game = CGT.par(STI)
        puts "CGT ⊗ STI = #{parallel_game.game}"
        
        # Both triads execute in parallel
        input = [:game_problem, :sheaf_problem]
        output = parallel_game.game.play.call(input)
        puts "Parallel play: #{input} → #{output.map { |o| o[:output] }}"
      end

      # Demonstrate adding a player
      def demo_add_player
        include Experts
        include Triads

        puts "\n=== Adding Player: Replace Hedges with Egolf in CGT ==="
        
        # This would violate GF(3) if we just swap
        # Instead, we need to find a compatible replacement
        
        # Create a new validator with same trit
        new_validator = ExpertPlayer.new(
          name: 'New Validator',
          trit: -1,
          expertise: 'formal-verification',
          interaction_weight: 1000
        )
        
        new_triad = CGT.add_player(new_validator, position: :validator)
        puts "Original: #{CGT}"
        puts "Modified: #{new_triad}"
        puts "GF(3) preserved: #{new_triad.balanced?}"
      end

      # Demonstrate removing a player
      def demo_remove_player
        include Triads

        puts "\n=== Removing Player: Remove Baez from CGT ==="
        
        dyad = CGT.remove_player(position: :coordinator)
        puts "Result: #{dyad}"
        puts "GF(3) deficit: need trit=#{dyad.gf3_deficit} to rebalance"
        
        # Rebalance with a new coordinator
        new_coordinator = Experts::SHULMAN
        rebalanced = dyad.rebalance_with(new_coordinator)
        puts "Rebalanced: #{rebalanced}"
      end

      # Full demonstration
      def demo_all
        demo_sequential_composition
        demo_parallel_composition
        demo_add_player
        demo_remove_player
      end
    end
  end
end

# Run if executed directly
if __FILE__ == $PROGRAM_NAME
  MusicTopos::InteractomeOpenGames.demo_all
end
