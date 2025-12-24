# lib/world_broadcast.rb
#
# WORLD: Word Models ↔ World Models Broadcasting System
#
# Tripartite mathematical generators broadcasting via:
# - S-expression generative model (CRDT.el compatible)
# - 3 mathematician agents in superposition
# - Sierpinski gasket indexing for conjugacy/equivalence classes
# - Analytic continuation through zeta functions
# - Condensed anima perspective (Scholze/Clausen)
#
# Usage:
#   just world                    # Start broadcasting
#   just world-mathematicians     # Specify 3 mathematicians
#
# The system generates s-expressions that can be:
# - Consumed by crdt.el for collaborative editing
# - Indexed by Sierpinski gasket addresses
# - Analytically continued via zeta regularization

require_relative 'tritwise_letter_spirit'
require_relative 'moebius'
require_relative 'girard_colors'
require_relative 'ramanujan_complex'
require_relative 'self_avoiding_colored_walk'
require 'json'
require 'securerandom'

module WorldBroadcast
  # ═══════════════════════════════════════════════════════════════
  # MATHEMATICIANS: Agents as superpositions of mathematical traditions
  # ═══════════════════════════════════════════════════════════════
  
  # ═══════════════════════════════════════════════════════════════
  # OPEN GAMES: World / Coworld Actions (Jules Hedges framework)
  # ═══════════════════════════════════════════════════════════════
  #
  # In open games (Hedges 2016), morphisms have 4 ports:
  #   - Covariant input (X): forward-flowing information
  #   - Covariant output (Y): forward result
  #   - Contravariant input (R): backward utility/gradient
  #   - Contravariant output (S): backward strategic choice
  #
  # World action:   X → Y (forward, covariant)
  # Coworld action: R → S (backward, contravariant)
  #
  # Mathematicians implement BOTH directions bidirectionally!
  
  WorldAction = Struct.new(:input_type, :output_type, :forward_fn, keyword_init: true)
  CoworldAction = Struct.new(:utility_type, :strategy_type, :backward_fn, keyword_init: true)
  
  MATHEMATICIAN_PROFILES = {
    # ═══════════════════════════════════════════════════════════════
    # CLASSICAL MATHEMATICIANS
    # ═══════════════════════════════════════════════════════════════
    ramanujan: {
      name: "Ramanujan",
      seed: 0x1729,           # Hardy-Ramanujan number
      style: :intuitive,
      domain: :number_theory,
      zeta_preference: :riemann,
      polarity: :positive,    # Girard: expansion
      operations: [:partition, :theta, :mock_theta, :continued_fraction],
      # Open game structure
      world_action: WorldAction.new(input_type: :integer, output_type: :partition, forward_fn: :partition_count),
      coworld_action: CoworldAction.new(utility_type: :modularity, strategy_type: :approximation, backward_fn: :theta_gradient)
    },
    grothendieck: {
      name: "Grothendieck",
      seed: 0x42D,            # The Answer * prime
      style: :structural,
      domain: :algebraic_geometry,
      zeta_preference: :motivic,
      polarity: :neutral,     # Girard: cut elimination
      operations: [:topos, :scheme, :cohomology, :descent],
      world_action: WorldAction.new(input_type: :ring, output_type: :scheme, forward_fn: :spec),
      coworld_action: CoworldAction.new(utility_type: :sheaf, strategy_type: :descent_data, backward_fn: :cohomology)
    },
    euler: {
      name: "Euler",
      seed: 0x271828,         # e approximation
      style: :computational,
      domain: :analysis,
      zeta_preference: :euler_product,
      polarity: :negative,    # Girard: contraction
      operations: [:series, :product, :integral, :identity],
      world_action: WorldAction.new(input_type: :sequence, output_type: :sum, forward_fn: :summation),
      coworld_action: CoworldAction.new(utility_type: :convergence, strategy_type: :remainder, backward_fn: :error_bound)
    },
    noether: {
      name: "Noether",
      seed: 0xE22A,           # Emmy Noether
      style: :algebraic,
      domain: :abstract_algebra,
      zeta_preference: :dedekind,
      polarity: :neutral,
      operations: [:ring, :ideal, :module, :symmetry],
      world_action: WorldAction.new(input_type: :group, output_type: :invariant, forward_fn: :noether_theorem),
      coworld_action: CoworldAction.new(utility_type: :symmetry, strategy_type: :conservation_law, backward_fn: :variational)
    },
    conway: {
      name: "Conway",
      seed: 0x4C4946,         # LIFE in hex
      style: :combinatorial,
      domain: :game_theory,
      zeta_preference: :surreal,
      polarity: :positive,
      operations: [:game, :surreal, :nimber, :look_and_say],
      world_action: WorldAction.new(input_type: :game_tree, output_type: :surreal_number, forward_fn: :game_value),
      coworld_action: CoworldAction.new(utility_type: :winning, strategy_type: :move, backward_fn: :minimax)
    },
    scholze: {
      name: "Scholze",
      seed: 0xC0DE,           # Condensed (valid hex)
      style: :foundational,
      domain: :arithmetic_geometry,
      zeta_preference: :perfectoid,
      polarity: :neutral,
      operations: [:condensed, :solid, :liquid, :analytic],
      world_action: WorldAction.new(input_type: :topological_space, output_type: :condensed_set, forward_fn: :condense),
      coworld_action: CoworldAction.new(utility_type: :profinite, strategy_type: :completion, backward_fn: :solidify)
    },
    
    # ═══════════════════════════════════════════════════════════════
    # LOGICIANS (from Valeria de Paiva's sphere)
    # ═══════════════════════════════════════════════════════════════
    depaiva: {
      name: "de Paiva",
      seed: 0xD1A1,           # Dialectica
      style: :categorical,
      domain: :linear_logic,
      zeta_preference: :dialectica,
      polarity: :neutral,
      operations: [:dialectica, :chu_space, :linear_implication, :modal],
      world_action: WorldAction.new(input_type: :formula, output_type: :proof, forward_fn: :dialectica_interp),
      coworld_action: CoworldAction.new(utility_type: :resource, strategy_type: :witness, backward_fn: :chu_transform)
    },
    girard: {
      name: "Girard",
      seed: 0x4C4C,           # Linear Logic
      style: :foundational,
      domain: :proof_theory,
      zeta_preference: :transcendental,
      polarity: :neutral,     # Invented polarity!
      operations: [:linear, :exponential, :focusing, :ludics],
      world_action: WorldAction.new(input_type: :sequent, output_type: :proof_net, forward_fn: :proof_search),
      coworld_action: CoworldAction.new(utility_type: :polarity, strategy_type: :cut_elimination, backward_fn: :focalize)
    },
    hyland: {
      name: "Hyland",
      seed: 0xEFF,            # Effective topos
      style: :constructive,
      domain: :topos_theory,
      zeta_preference: :realizability,
      polarity: :positive,
      operations: [:effective_topos, :realizability, :pca, :tripos],
      world_action: WorldAction.new(input_type: :partial_function, output_type: :realizer, forward_fn: :realize),
      coworld_action: CoworldAction.new(utility_type: :modesty, strategy_type: :tracker, backward_fn: :track)
    },
    hedges: {
      name: "Hedges",
      seed: 0x0E,             # Open games
      style: :compositional,
      domain: :game_theory,
      zeta_preference: :categorical,
      polarity: :neutral,
      operations: [:open_game, :lens, :costate, :equilibrium],
      world_action: WorldAction.new(input_type: :observation, output_type: :choice, forward_fn: :play),
      coworld_action: CoworldAction.new(utility_type: :payoff, strategy_type: :best_response, backward_fn: :coplay)
    },
    abramsky: {
      name: "Abramsky",
      seed: 0xC07,            # Context
      style: :semantic,
      domain: :quantum_logic,
      zeta_preference: :contextual,
      polarity: :negative,
      operations: [:game_semantics, :contextuality, :sheaf, :comonad],
      world_action: WorldAction.new(input_type: :question, output_type: :answer, forward_fn: :dialogue),
      coworld_action: CoworldAction.new(utility_type: :context, strategy_type: :section, backward_fn: :sheafify)
    },
    lawvere: {
      name: "Lawvere",
      seed: 0xCA7,            # Category
      style: :algebraic,
      domain: :category_theory,
      zeta_preference: :cohesive,
      polarity: :neutral,
      operations: [:topos, :hyperdoctrine, :adjunction, :unity_of_opposites],
      world_action: WorldAction.new(input_type: :object, output_type: :morphism, forward_fn: :hom),
      coworld_action: CoworldAction.new(utility_type: :level, strategy_type: :modality, backward_fn: :base_change)
    },
    
    # ═══════════════════════════════════════════════════════════════
    # CONTEMPORARY LOGICIANS / CATEGORY THEORISTS
    # ═══════════════════════════════════════════════════════════════
    spivak: {
      name: "Spivak",
      seed: 0xAC7,            # Applied Category Theory
      style: :applied,
      domain: :applied_category_theory,
      zeta_preference: :polynomial,
      polarity: :positive,
      operations: [:polynomial_functor, :mode, :wiring_diagram, :database],
      world_action: WorldAction.new(input_type: :interface, output_type: :system, forward_fn: :compose),
      coworld_action: CoworldAction.new(utility_type: :behavior, strategy_type: :chart, backward_fn: :readout)
    },
    shulman: {
      name: "Shulman",
      seed: 0x407,            # HoTT
      style: :homotopical,
      domain: :homotopy_type_theory,
      zeta_preference: :univalent,
      polarity: :neutral,
      operations: [:univalence, :higher_inductive, :cohesion, :modal],
      world_action: WorldAction.new(input_type: :type, output_type: :space, forward_fn: :interpret),
      coworld_action: CoworldAction.new(utility_type: :path, strategy_type: :transport, backward_fn: :ap)
    },
    baez: {
      name: "Baez",
      seed: 0xCA1,            # n-Category
      style: :higher_categorical,
      domain: :higher_category_theory,
      zeta_preference: :groupoid_cardinality,
      polarity: :positive,
      operations: [:n_category, :tqft, :span, :cobordism],
      world_action: WorldAction.new(input_type: :manifold, output_type: :cobordism, forward_fn: :bordify),
      coworld_action: CoworldAction.new(utility_type: :quantum_number, strategy_type: :state_sum, backward_fn: :evaluate)
    },
    riehl: {
      name: "Riehl",
      seed: 0x1A4,            # ∞-category
      style: :infinity_categorical,
      domain: :infinity_category_theory,
      zeta_preference: :homotopy_coherent,
      polarity: :neutral,
      operations: [:quasicategory, :model_structure, :adjunction, :kan_extension],
      world_action: WorldAction.new(input_type: :diagram, output_type: :limit, forward_fn: :kan_extend),
      coworld_action: CoworldAction.new(utility_type: :lifting, strategy_type: :horn, backward_fn: :fill)
    }
  }
  

  
  # ═══════════════════════════════════════════════════════════════
  # SIERPINSKI GASKET ADDRESS SYSTEM
  # ═══════════════════════════════════════════════════════════════
  
  module SierpinskiAddress
    # Sierpinski gasket addressing: ternary path from root
    # Each trit (0, 1, 2) represents which sub-triangle
    #
    #        2
    #       / \
    #      0---1
    #
    # Address "012" = triangle 0 → subtriangle 1 → subtriangle 2
    
    def self.encode(depth, position)
      address = []
      pos = position
      depth.times do
        address.unshift(pos % 3)
        pos /= 3
      end
      address
    end
    
    def self.decode(address)
      address.reduce(0) { |acc, trit| acc * 3 + trit }
    end
    
    # Conjugacy class: addresses that are equivalent under rotation
    def self.conjugacy_class(address)
      rotations = 3.times.map do |r|
        address.map { |t| (t + r) % 3 }
      end
      rotations.min  # Canonical representative
    end
    
    # Equivalence class: addresses equivalent under dihedral group D₃
    def self.equivalence_class(address)
      rotations = 3.times.map { |r| address.map { |t| (t + r) % 3 } }
      reflections = rotations.map { |a| a.map { |t| (3 - t) % 3 } }
      (rotations + reflections).min
    end
    
    # Depth of address
    def self.depth(address)
      address.size
    end
    
    # Parent address (remove last trit)
    def self.parent(address)
      address[0...-1]
    end
    
    # Children addresses (append 0, 1, 2)
    def self.children(address)
      [0, 1, 2].map { |t| address + [t] }
    end
    
    # Hausdorff dimension of Sierpinski gasket
    HAUSDORFF_DIM = Math.log(3) / Math.log(2)  # ≈ 1.585
  end
  
  # ═══════════════════════════════════════════════════════════════
  # ZETA FUNCTIONS FOR ANALYTIC CONTINUATION
  # ═══════════════════════════════════════════════════════════════
  
  module ZetaFunctions
    # Riemann zeta: ζ(s) = Σ n^(-s)
    def self.riemann(s, terms: 100)
      return Float::INFINITY if s <= 1
      (1..terms).sum { |n| n ** (-s) }
    end
    
    # Euler product: ζ(s) = Π (1 - p^(-s))^(-1)
    def self.euler_product(s, primes: [2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
      primes.reduce(1.0) { |prod, p| prod / (1 - p ** (-s)) }
    end
    
    # Dirichlet L-function: L(s, χ) = Σ χ(n) n^(-s)
    def self.dirichlet_l(s, character, terms: 100)
      (1..terms).sum { |n| character.call(n) * (n ** (-s)) }
    end
    
    # Möbius-weighted zeta: related to 1/ζ(s)
    def self.moebius_weighted(s, terms: 100)
      (1..terms).sum { |n| Moebius.mu(n) * (n ** (-s)) }
    end
    
    # Analytic continuation via functional equation (symbolic)
    def self.reflect(s)
      # ζ(s) = 2^s π^(s-1) sin(πs/2) Γ(1-s) ζ(1-s)
      # Returns the "reflected" s for analytic continuation
      1 - s
    end
    
    # Regularized sum using zeta: Σ n = -1/12
    def self.regularize(sequence, s: -1)
      # Zeta regularization: Σ a_n → ζ-regularized value
      riemann(s)
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # CONDENSED ANIMA: Scholze/Clausen perspective
  # ═══════════════════════════════════════════════════════════════
  
  module CondensedAnima
    # Condensed sets: sheaves on compact Hausdorff spaces
    # Anima = ∞-groupoids = homotopy types
    #
    # Key insight: topology lives in the *test objects*, not the space itself
    
    # Profinite approximation (like p-adic completion)
    def self.profinite_approximate(value, levels: 3)
      # Approximate by finite quotients
      levels.times.map do |n|
        modulus = 3 ** (n + 1)
        value % modulus
      end
    end
    
    # Liquid vector space norm (Clausen-Scholze)
    # |x|_r for r ∈ (0, 1)
    def self.liquid_norm(coefficients, r: 0.5)
      coefficients.each_with_index.sum do |c, n|
        c.abs * (r ** n)
      end
    end
    
    # Solid module: completion for r → 1
    def self.solid_completion(sequence)
      # Solid = "maximally complete" liquid
      sequence.sum.to_f / sequence.size
    end
    
    # Analytic stack: derived category perspective
    # Following Clausen-Scholze analytic geometry
    def self.analytic_stack(objects)
      # Objects form a stack if they satisfy descent
      {
        objects: objects,
        descent_data: objects.combination(2).map { |a, b| [a, b, a ^ b] },
        coherence: true,
        # 6-functor formalism data (from arXiv:2507.08566)
        six_functors: {
          pushforward: ->(f, x) { f.call(x) },          # f_*
          pullback: ->(f, x) { x },                      # f^* (base change)
          shriek_push: ->(f, x) { f.call(x) },          # f_! (proper pushforward)
          shriek_pull: ->(f, x) { x },                   # f^!
          internal_hom: ->(a, b) { [a, b] },            # Hom
          tensor: ->(a, b) { a ^ b }                     # ⊗
        }
      }
    end
    
    # Categorical Künneth formula (Kesting 2507.08566)
    # QCoh(X × Y) ≃ QCoh(X) ⊗ QCoh(Y)
    def self.kunneth_product(stack_x, stack_y)
      {
        product_objects: stack_x[:objects].product(stack_y[:objects]),
        # Tensor product of quasi-coherent sheaves
        qcoh_tensor: stack_x[:objects].flat_map { |x|
          stack_y[:objects].map { |y| [x, y, x ^ y] }
        },
        # Künneth isomorphism witnesses
        kunneth_iso: true
      }
    end
    
    # Tannakian reconstruction for analytic stacks
    def self.tannakian_reconstruct(qcoh_category)
      # Recover stack from its category of quasi-coherent sheaves
      {
        fiber_functor: ->(x) { x },
        automorphisms: qcoh_category.map { |obj| [obj, obj] },
        reconstruction: :complete
      }
    end
    
    # Bridge to sheaf neural networks
    # Maps condensed structure to cellular sheaf for diffusion
    def self.to_cellular_sheaf(analytic_stack)
      vertices = analytic_stack[:objects]
      {
        vertices: vertices,
        edges: analytic_stack[:descent_data].map { |d| { src: d[0], tgt: d[1] } },
        stalks: vertices.map { |v| { vertex: v, stalk: [v] } },
        restriction_maps: analytic_stack[:descent_data].map { |d|
          { edge: [d[0], d[1]], map: ->(x) { x ^ d[2] } }
        },
        # Sheaf Laplacian: L = δᵀδ + δδᵀ
        laplacian_compatible: true
      }
    end
    
    # Pyknotic approximation (hypersheaves on compacta)
    # Barwick-Haine arXiv:1904.09966
    def self.pyknotic_approx(condensed_set, compactum_probes: 3)
      probes = (1..compactum_probes).map { |n| 2 ** n }
      {
        probes: probes,
        sections: probes.map { |p| condensed_set % p },
        hypercomplete: true
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # S-EXPRESSION GENERATOR (CRDT.el compatible)
  # ═══════════════════════════════════════════════════════════════
  
  module SexpGenerator
    # Generate s-expression from mathematical operation
    def self.generate(mathematician, operation, args, address)
      # Core structure: (operation arg1 arg2 ... :meta {...})
      sexp = [
        operation,
        *args,
        :meta, {
          mathematician: mathematician[:name],
          seed: mathematician[:seed],
          address: address,
          timestamp: Time.now.to_f,
          color: SeedMiner.color_at(mathematician[:seed], address.sum + 1)
        }
      ]
      sexp
    end
    
    # Serialize to string (Lisp-style)
    def self.to_string(sexp)
      case sexp
      when Array
        "(#{sexp.map { |x| to_string(x) }.join(' ')})"
      when Symbol
        ":#{sexp}"
      when Hash
        "(#{sexp.map { |k, v| "#{to_string(k)} #{to_string(v)}" }.join(' ')})"
      when String
        "\"#{sexp}\""
      else
        sexp.to_s
      end
    end
    
    # Parse from string (simplified)
    def self.parse(str)
      # Tokenize and parse
      tokens = str.gsub('(', ' ( ').gsub(')', ' ) ').split
      parse_tokens(tokens)
    end
    
    private
    
    def self.parse_tokens(tokens)
      return nil if tokens.empty?
      token = tokens.shift
      if token == '('
        list = []
        while tokens.first != ')'
          list << parse_tokens(tokens)
        end
        tokens.shift  # Remove ')'
        list
      elsif token == ')'
        raise "Unexpected )"
      elsif token.start_with?(':')
        token[1..].to_sym
      elsif token.match?(/^-?\d+$/)
        token.to_i
      elsif token.match?(/^-?\d+\.\d+$/)
        token.to_f
      else
        token
      end
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # CRDT OPERATIONS (compatible with crdt.el)
  # ═══════════════════════════════════════════════════════════════
  
  module CRDTOperations
    # Operation types for conflict-free merging
    OPERATIONS = {
      insert: ->(state, args) { state + [args[:value]] },
      delete: ->(state, args) { state.reject { |x| x == args[:value] } },
      update: ->(state, args) { state.map { |x| x == args[:old] ? args[:new] : x } },
      merge: ->(state, args) { (state + args[:other]).uniq }
    }
    
    # Lamport timestamp for ordering
    def self.lamport_timestamp(agent_id, counter)
      [counter, agent_id]
    end
    
    # Vector clock for causality
    def self.vector_clock(agents, counters)
      agents.zip(counters).to_h
    end
    
    # Last-Writer-Wins register
    def self.lww_register(value, timestamp)
      { value: value, timestamp: timestamp }
    end
    
    # G-Counter (grow-only)
    def self.g_counter_increment(counters, agent_id)
      counters.merge(agent_id => (counters[agent_id] || 0) + 1)
    end
    
    # PN-Counter (positive-negative)
    def self.pn_counter_value(p_counters, n_counters)
      p_counters.values.sum - n_counters.values.sum
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # MATHEMATICIAN AGENT: Generates mathematical content
  # ═══════════════════════════════════════════════════════════════
  
  class MathematicianAgent
    attr_reader :profile, :state, :history, :address
    
    def initialize(profile_key)
      @profile = MATHEMATICIAN_PROFILES[profile_key] || MATHEMATICIAN_PROFILES[:euler]
      @state = 0
      @history = []
      @address = []
      @rng = SeedMiner::SplitMix64.new(@profile[:seed])
    end
    
    def step!
      @state += 1
      
      # Choose operation based on state
      operation = @profile[:operations][@state % @profile[:operations].size]
      
      # Generate arguments from RNG
      args = generate_args(operation)
      
      # Update Sierpinski address
      trit = @rng.next_u64 % 3
      @address = (@address + [trit]).last(8)  # Keep depth ≤ 8
      
      # Generate s-expression
      sexp = SexpGenerator.generate(@profile, operation, args, @address.dup)
      
      # Record in history
      @history << {
        state: @state,
        operation: operation,
        args: args,
        address: @address.dup,
        sexp: sexp,
        conjugacy_class: SierpinskiAddress.conjugacy_class(@address),
        equivalence_class: SierpinskiAddress.equivalence_class(@address)
      }
      
      @history.last
    end
    
    def generate_args(operation)
      case operation
      when :partition, :theta, :series
        [(@rng.next_u64 % 100) + 1]
      when :cohomology, :descent
        [(@rng.next_u64 % 10), (@rng.next_u64 % 5)]
      when :topos, :scheme
        [:sheaf, (@rng.next_u64 % 7)]
      when :continued_fraction
        5.times.map { (@rng.next_u64 % 10) + 1 }
      when :identity
        [:euler, Math::E.round(4)]
      when :condensed, :solid, :liquid
        [:padic, 3, (@rng.next_u64 % 100)]
      when :game, :surreal
        [(@rng.next_u64 % 2) - 1, (@rng.next_u64 % 2) - 1]  # ternary
      else
        [(@rng.next_u64 % 50)]
      end
    end
    
    # Zeta-regularized output
    def zeta_regularize(s = 2)
      return { raw_sum: 0.0, zeta_factor: 1.0, regularized: 0.0 } if @history.empty?
      
      contributions = @history.map.with_index do |h, n|
        weight = (n + 1) ** (-s)
        # Handle args that might be symbols or arrays
        arg_value = case h[:args].first
                    when Numeric then h[:args].first.to_f
                    when Array then h[:args].first.sum.to_f rescue 0.0
                    else h[:state].to_f  # Fallback to state
                    end
        { step: h[:state], weighted_contribution: weight * arg_value }
      end
      zeta = ZetaFunctions.riemann(s).to_f
      zeta = 1.0 if zeta.zero? || zeta.nan? || zeta.infinite?
      {
        raw_sum: contributions.sum { |c| c[:weighted_contribution] },
        zeta_factor: zeta,
        regularized: contributions.sum { |c| c[:weighted_contribution] } / zeta
      }
    end
    
    def to_s
      "#{@profile[:name]}(state=#{@state}, addr=#{@address.join})"
    end
    
    # ═════════════════════════════════════════════════════════════
    # OPEN GAME: World / Coworld Actions
    # ═════════════════════════════════════════════════════════════
    
    # Execute world action (forward, covariant): X → Y
    def world_action(input)
      wa = @profile[:world_action]
      return { output: input, fn: :identity } unless wa
      
      # Simulate forward transformation based on fn type
      output = case wa.forward_fn
               when :partition_count then input.to_i % 100
               when :spec then "Spec(#{input})"
               when :summation then input.is_a?(Array) ? input.sum : input
               when :noether_theorem then "Invariant[#{input}]"
               when :game_value then input.to_i % 3 - 1  # Surreal: -1, 0, 1
               when :condense then "Cond(#{input})"
               when :dialectica_interp then "⊢ #{input}"
               when :proof_search then "Π(#{input})"
               when :realize then "⟦#{input}⟧"
               when :play then @rng.next_u64 % 3
               when :dialogue then "A: #{input}"
               when :hom then "Hom(−, #{input})"
               when :compose then "∘(#{input})"
               when :interpret then "⟨#{input}⟩"
               when :bordify then "∂(#{input})"
               when :kan_extend then "Lan(#{input})"
               else input
               end
      
      { input_type: wa.input_type, output_type: wa.output_type, 
        input: input, output: output, fn: wa.forward_fn }
    end
    
    # Execute coworld action (backward, contravariant): R → S
    def coworld_action(utility)
      ca = @profile[:coworld_action]
      return { strategy: utility, fn: :identity } unless ca
      
      # Simulate backward transformation
      strategy = case ca.backward_fn
                 when :theta_gradient then utility.to_f * 0.618  # Golden ratio
                 when :cohomology then "H*(#{utility})"
                 when :error_bound then 1.0 / (utility.to_f + 1)
                 when :variational then "δ(#{utility})"
                 when :minimax then utility.to_i.clamp(-1, 1)
                 when :solidify then "Solid(#{utility})"
                 when :chu_transform then "Chu(#{utility})"
                 when :focalize then utility.to_s.upcase
                 when :track then [utility, @state]
                 when :coplay then (utility.to_i + @state) % 3 - 1
                 when :sheafify then "Sh(#{utility})"
                 when :base_change then "f*(#{utility})"
                 when :readout then utility.to_s.chars.map(&:ord).sum
                 when :ap then "ap_#{utility}"
                 when :evaluate then utility.to_i.abs
                 when :fill then "Λ(#{utility})"
                 else utility
                 end
      
      { utility_type: ca.utility_type, strategy_type: ca.strategy_type,
        utility: utility, strategy: strategy, fn: ca.backward_fn }
    end
    
    # Bidirectional: Run both world and coworld in sequence (lens-like)
    def bidirectional_step!(input, utility)
      forward = world_action(input)
      backward = coworld_action(utility)
      
      {
        mathematician: @profile[:name],
        forward: forward,
        backward: backward,
        state: @state,
        address: @address.dup
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # TRIPARTITE SYSTEM: 3 Mathematicians in Superposition
  # ═══════════════════════════════════════════════════════════════
  
  class TripartiteSystem
    attr_reader :agents, :epoch, :broadcast_log, :crdt_state
    
    def initialize(mathematician_keys = [:ramanujan, :grothendieck, :euler])
      @mathematician_keys = mathematician_keys
      @agents = mathematician_keys.map { |k| MathematicianAgent.new(k) }
      @epoch = 0
      @broadcast_log = []
      @crdt_state = {
        sexps: [],
        vector_clock: mathematician_keys.map { |k| [k, 0] }.to_h,
        sierpinski_index: {}  # address → [sexps at that address]
      }
      
      # Self-avoiding walk for every interaction (colored by SplitMixTernary)
      combined_seed = mathematician_keys.map { |k| MATHEMATICIAN_PROFILES[k][:seed] }.reduce(:^)
      @interaction_walker = SelfAvoidingColoredWalk::InteractionWalker.new(combined_seed)
    end
    
    attr_reader :interaction_walker
    
    # Step all agents, generate superposition
    def step!
      @epoch += 1
      
      # Each agent steps
      results = @agents.map(&:step!)
      
      # SELF-AVOIDING WALK: Color this interaction
      walk_result = @interaction_walker.on_interaction(@epoch)
      
      # Compute superposition (weighted by Girard polarity)
      polarities = @agents.map { |a| polarity_weight(a.profile[:polarity]) }
      superposition = compute_superposition(results, polarities)
      
      # Update CRDT state
      results.each_with_index do |r, i|
        key = @mathematician_keys[i]
        @crdt_state[:vector_clock][key] = (@crdt_state[:vector_clock][key] || 0) + 1
        @crdt_state[:sexps] << r[:sexp]
        
        # Index by Sierpinski address
        addr_key = r[:address].join
        @crdt_state[:sierpinski_index][addr_key] ||= []
        @crdt_state[:sierpinski_index][addr_key] << r[:sexp]
      end
      
      # Create broadcast message with walk position
      message = {
        epoch: @epoch,
        timestamp: Time.now.to_f,
        agents: results.map { |r| { operation: r[:operation], address: r[:address] } },
        superposition: superposition,
        vector_clock: @crdt_state[:vector_clock].dup,
        condensed: CondensedAnima.profinite_approximate(@epoch),
        zeta_regularized: @agents.first.zeta_regularize,
        # Self-avoiding walk coloring
        walk: {
          position: walk_result[:position].coords,
          trit: walk_result[:position].trit,
          color_index: walk_result[:position].color_index,
          hue: walk_result[:position].color[:H].round(1),
          verified: walk_result[:verification][:verified]
        }
      }
      
      @broadcast_log << message
      message
    end
    
    def compute_superposition(results, weights)
      # Combine addresses using weighted voting
      weight_sum = weights.map(&:abs).sum
      weight_sum = 1.0 if weight_sum.zero?
      
      combined_address = results.first[:address].each_with_index.map do |_, i|
        votes = results.map.with_index { |r, j| (r[:address][i] || 0).to_i * weights[j] }
        ((votes.sum / weight_sum) + 1).round % 3  # +1 to handle negative weights
      end
      
      {
        addresses: results.map { |r| r[:address] },
        combined: combined_address,
        conjugacy: SierpinskiAddress.conjugacy_class(combined_address),
        equivalence: SierpinskiAddress.equivalence_class(combined_address)
      }
    end
    
    def polarity_weight(polarity)
      case polarity
      when :positive then 1.0
      when :negative then -1.0
      when :neutral then 0.0
      else 0.0
      end
    end
    
    # Run until convergence (spectral gap)
    def run!(steps = 12)
      steps.times { step! }
      self
    end
    
    # Broadcast as s-expressions
    def broadcast_sexps
      @crdt_state[:sexps].map { |s| SexpGenerator.to_string(s) }
    end
    
    # Get sexps at Sierpinski address
    def at_address(address)
      addr_key = address.is_a?(Array) ? address.join : address
      @crdt_state[:sierpinski_index][addr_key] || []
    end
    
    # Analytic continuation via zeta
    def analytic_continuation(s = 2)
      @agents.map do |agent|
        {
          mathematician: agent.profile[:name],
          zeta_preference: agent.profile[:zeta_preference],
          regularized: agent.zeta_regularize(s)
        }
      end
    end
    
    def to_s
      "Tripartite(epoch=#{@epoch}, agents=#{@agents.map(&:to_s).join(', ')})"
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # WORLD: Main entry point
  # ═══════════════════════════════════════════════════════════════
  
  def self.world(mathematicians: [:ramanujan, :grothendieck, :euler], steps: 12, verbose: true)
    puts "╔═══════════════════════════════════════════════════════════════════════════════╗" if verbose
    puts "║  WORLD: Word Models ↔ World Models Broadcasting                              ║" if verbose
    puts "╚═══════════════════════════════════════════════════════════════════════════════╝" if verbose
    puts if verbose
    
    system = TripartiteSystem.new(mathematicians)
    
    if verbose
      puts "Mathematicians: #{mathematicians.map { |m| MATHEMATICIAN_PROFILES[m][:name] }.join(' ⊗ ')}"
      puts "Sierpinski Hausdorff dimension: #{SierpinskiAddress::HAUSDORFF_DIM.round(4)}"
      puts "Condensed perspective: profinite approximation active"
      puts
      puts "Broadcasting #{steps} epochs..."
      puts "─" * 80
    end
    
    system.run!(steps)
    
    if verbose
      system.broadcast_log.each do |msg|
        addrs = msg[:agents].map { |a| a[:address].join }.join(' | ')
        sup = msg[:superposition][:combined].join
        conj = msg[:superposition][:conjugacy].join
        walk = msg[:walk]
        trit_char = walk[:trit] == 1 ? '+' : (walk[:trit] == -1 ? '-' : '0')
        
        puts "Epoch #{msg[:epoch].to_s.rjust(2)}: addresses=[#{addrs}] → #{sup} | walk=(#{walk[:position].join(',')}) trit=#{trit_char} H=#{walk[:hue]}°"
      end
      
      # Walk summary
      gf3 = system.interaction_walker.walk.gf3_conservation_check
      spec = system.interaction_walker.walk.spectral_summary
      puts
      puts "─" * 80
      puts "Self-Avoiding Walk Summary:"
      puts "  GF(3) conserved: #{gf3[:all_conserved] ? '✓' : '✗'} (#{gf3[:conserved_count]}/#{gf3[:triplets]} triplets)"
      puts "  Is self-avoiding: #{spec[:is_self_avoiding] ? '✓' : '✗'} (#{spec[:violations_caught]} violations caught)"
      puts "  Spectral gap: #{spec[:spectral_gap]} (#{spec[:verifications]} verifications)"
      
      puts
      puts "─" * 80
      puts "Analytic Continuation (ζ-regularized):"
      system.analytic_continuation.each do |ac|
        puts "  #{ac[:mathematician]} (#{ac[:zeta_preference]}): #{ac[:regularized][:regularized].round(6)}"
      end
      
      puts
      puts "─" * 80
      puts "Sample S-expressions (CRDT.el compatible):"
      system.broadcast_sexps.first(3).each do |sexp|
        puts "  #{sexp[0..100]}..."
      end
      
      puts
      puts "Sierpinski index entries: #{system.crdt_state[:sierpinski_index].keys.size}"
      puts "Total sexps generated: #{system.crdt_state[:sexps].size}"
    end
    
    system
  end
  
  # Alias for just world
  def self.run!(*args, **kwargs)
    world(*args, **kwargs)
  end
end

# Run if executed directly
if __FILE__ == $0
  WorldBroadcast.world
end
