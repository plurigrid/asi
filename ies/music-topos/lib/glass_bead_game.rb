# lib/glass_bead_game.rb
#
# GLASS BEAD GAME: Hesse-inspired Interdisciplinary Synthesis
#
# Implements the Glasperlenspiel with:
# - Badiou triangle inequality for world hopping
# - Propagator-based epistemic arbitrage
# - Integration with WorldBroadcast mathematicians
# - NATS/Synadia distributed play
#
# Mathematical Foundation:
#   Being → Event → Truth (Badiou)
#   d(W₁, W₃) ≤ d(W₁, W₂) + d(W₂, W₃) (Triangle Inequality)
#
# Usage:
#   just glass-bead          # Interactive game
#   just world-hop w1 w2     # Hop between worlds

require_relative 'world_broadcast'
require_relative 'girard_colors'
require_relative 'moebius'
require 'json'
require 'securerandom'

module GlassBeadGame
  # ═══════════════════════════════════════════════════════════════
  # SPLITMIX TERNARY (Parallel-safe RNG with -1, 0, +1 outputs)
  # ═══════════════════════════════════════════════════════════════
  
  class SplitMixTernary
    GOLDEN = 0x9e3779b97f4a7c15
    
    def initialize(seed)
      @state = seed & 0xFFFFFFFFFFFFFFFF
    end
    
    def next_u64
      @state = (@state + GOLDEN) & 0xFFFFFFFFFFFFFFFF
      z = @state
      z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & 0xFFFFFFFFFFFFFFFF
      z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & 0xFFFFFFFFFFFFFFFF
      z ^ (z >> 31)
    end
    
    def next_ternary
      (next_u64 % 3) - 1  # -1, 0, or +1
    end
    
    def next_float
      next_u64.to_f / 0xFFFFFFFFFFFFFFFF.to_f
    end
    
    def split(index)
      child_seed = @state ^ (index * GOLDEN)
      SplitMixTernary.new(child_seed)
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # BEAD: Fundamental unit of the game
  # ═══════════════════════════════════════════════════════════════
  
  class Bead
    DOMAINS = [:mathematics, :music, :philosophy, :physics, :art, :language]
    
    attr_reader :domain, :concept, :seed, :color, :metadata
    
    def initialize(domain, concept, seed: nil, metadata: {})
      @domain = domain.to_sym
      @concept = concept
      @seed = seed || concept.hash
      @color = SeedMiner.color_at(@seed, 1)
      @metadata = metadata
    end
    
    def complexity
      @concept.to_s.length + @metadata.keys.length
    end
    
    def near_void?
      complexity < 5
    end
    
    def to_h
      { domain: @domain, concept: @concept, seed: @seed, color: @color[:hex] }
    end
    
    def to_s
      "#{@domain}:#{@concept}"
    end
    
    def ==(other)
      @domain == other.domain && @concept == other.concept
    end
    
    def hash
      [@domain, @concept].hash
    end
    
    alias eql? ==
  end
  
  # ═══════════════════════════════════════════════════════════════
  # POSSIBLE WORLD: Configuration in possibility space
  # ═══════════════════════════════════════════════════════════════
  
  class PossibleWorld
    attr_reader :seed, :epoch, :beads, :invariants, :state
    attr_accessor :accessibility
    
    def initialize(seed:, epoch: 0, beads: [], invariants: [])
      @seed = seed
      @epoch = epoch
      @beads = beads
      @invariants = invariants
      @accessibility = {}
      @rng = SplitMixTernary.new(seed + epoch)
      @state = compute_state
    end
    
    def compute_state
      {
        color: SeedMiner.color_at(@seed, @epoch + 1),
        polarity: [:positive, :negative, :neutral][@rng.next_ternary + 1],
        energy: @rng.next_float,
        mathematician: select_mathematician
      }
    end
    
    def select_mathematician
      keys = WorldBroadcast::MATHEMATICIAN_PROFILES.keys
      keys[@rng.next_u64 % keys.size]
    end
    
    def add_bead(bead)
      @beads << bead unless @beads.include?(bead)
      self
    end
    
    def add_invariant(inv)
      @invariants << inv unless @invariants.include?(inv)
      self
    end
    
    def advance!
      @epoch += 1
      @rng = SplitMixTernary.new(@seed + @epoch)
      @state = compute_state
      self
    end
    
    def fork(event_seed)
      new_seed = @seed ^ event_seed
      PossibleWorld.new(
        seed: new_seed,
        epoch: @epoch + 1,
        beads: @beads.dup,
        invariants: @invariants.select { |inv| inv.is_a?(Symbol) }
      )
    end
    
    def to_h
      {
        seed: @seed,
        epoch: @epoch,
        state: @state,
        beads: @beads.map(&:to_h),
        invariants: @invariants
      }
    end
    
    def to_s
      "World(seed=0x#{@seed.to_s(16)}, epoch=#{@epoch}, beads=#{@beads.size})"
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # BADIOU TRIANGLE: Distance metric for world hopping
  # ═══════════════════════════════════════════════════════════════
  
  module BadiouTriangle
    # Hamming distance between seeds
    def self.hamming_distance(a, b)
      (a ^ b).to_s(2).count('1')
    end
    
    # World distance: Being + Event + Truth components
    def self.world_distance(w1, w2)
      # Being: ontological difference (seed divergence)
      being = hamming_distance(w1.seed, w2.seed).to_f / 64.0 * 10
      
      # Event: temporal separation
      event = (w1.epoch - w2.epoch).abs.to_f
      
      # Truth: invariant divergence
      shared = (w1.invariants & w2.invariants).size
      total = (w1.invariants | w2.invariants).size
      truth = total > 0 ? (1.0 - shared.to_f / total) * 10 : 0.0
      
      Math.sqrt(being**2 + event**2 + truth**2)
    end
    
    # Triangle inequality check
    def self.valid_triangle?(w1, w2, w3)
      d12 = world_distance(w1, w2)
      d23 = world_distance(w2, w3)
      d13 = world_distance(w1, w3)
      
      d13 <= d12 + d23 + 0.001  # Small epsilon for floating point
    end
    
    # Find shortest path via Dijkstra with triangle pruning
    def self.shortest_path(start, target, worlds)
      distances = { start.seed => 0.0 }
      previous = {}
      visited = Set.new
      queue = [start]
      
      while queue.any?
        current = queue.min_by { |w| distances[w.seed] || Float::INFINITY }
        queue.delete(current)
        
        break if current.seed == target.seed
        next if visited.include?(current.seed)
        visited << current.seed
        
        worlds.each do |neighbor|
          next if visited.include?(neighbor.seed)
          
          d = distances[current.seed] + world_distance(current, neighbor)
          
          # Triangle inequality pruning
          if valid_triangle?(start, current, neighbor)
            if distances[neighbor.seed].nil? || d < distances[neighbor.seed]
              distances[neighbor.seed] = d
              previous[neighbor.seed] = current
              queue << neighbor unless queue.include?(neighbor)
            end
          end
        end
      end
      
      # Reconstruct path
      path = []
      current = target
      while previous[current.seed]
        path.unshift(current)
        current = previous[current.seed]
      end
      path.unshift(start) if current.seed == start.seed
      
      { path: path, distance: distances[target.seed] || Float::INFINITY }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # EVENT: Badiou-style rupture creating new possibilities
  # ═══════════════════════════════════════════════════════════════
  
  class Event
    attr_reader :site, :name, :seed
    
    def initialize(site:, name:)
      @site = site.is_a?(Array) ? site : [site]
      @name = name
      @seed = name.hash
    end
    
    def occurs?(world)
      # Event occurs if site contains elements "on the edge of void"
      @site.any? do |s|
        case s
        when :color then world.state[:color][:L] < 20  # Dark = near void
        when :polarity then world.state[:polarity] == :neutral
        when :beads then world.beads.any?(&:near_void?)
        else false
        end
      end
    end
    
    def execute!(world)
      return nil unless occurs?(world)
      
      new_world = world.fork(@seed)
      new_world.add_invariant(@name)
      new_world
    end
    
    def to_s
      "Event(#{@name}, site=#{@site})"
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # MOVES: Game actions
  # ═══════════════════════════════════════════════════════════════
  
  module Move
    class Base
      attr_reader :from, :to, :metadata
      
      def initialize(from:, to: nil, **metadata)
        @from = from
        @to = to
        @metadata = metadata
      end
      
      def execute!(game)
        raise NotImplementedError
      end
      
      def points
        raise NotImplementedError
      end
    end
    
    class Connect < Base
      attr_reader :via
      
      def initialize(from:, to:, via:, **metadata)
        super(from: from, to: to, **metadata)
        @via = via
      end
      
      def execute!(game)
        game.add_connection(@from, @to, @via)
      end
      
      def points
        base = 10
        cross_domain = @from.domain != @to.domain
        base * (cross_domain ? 2 : 1)
      end
    end
    
    class Transpose < Base
      attr_reader :structure, :from_domain, :to_domain, :functor
      
      def initialize(structure:, from_domain:, to_domain:, functor:)
        @structure = structure
        @from_domain = from_domain
        @to_domain = to_domain
        @functor = functor
        super(from: nil, to: nil)
      end
      
      def execute!(game)
        # Apply functor to transpose structure
        game.transpose_structure(@structure, @from_domain, @to_domain, @functor)
      end
      
      def points
        25 * 3  # Structure-preserving bonus
      end
    end
    
    class Hop < Base
      attr_reader :event, :truth_preserved
      
      def initialize(from_world:, event:, to_world: nil, truth_preserved: nil)
        @event = event.is_a?(Event) ? event : Event.new(site: [:polarity], name: event.to_s)
        @truth_preserved = truth_preserved
        super(from: from_world, to: to_world)
      end
      
      def execute!(game)
        new_world = @event.execute!(@from)
        return nil unless new_world
        
        @to = new_world
        game.add_world(new_world)
        new_world
      end
      
      def points
        return 0 unless @to
        distance = BadiouTriangle.world_distance(@from, @to)
        elegance = distance > 0 ? 1.0 / distance : 1.0
        (50 * [elegance, 1.0].min).to_i
      end
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # PROPAGATOR CELL: For epistemic arbitrage
  # ═══════════════════════════════════════════════════════════════
  
  class PropagatorCell
    attr_reader :domain, :knowledge, :connections
    
    def initialize(domain, initial_knowledge: 0.0)
      @domain = domain
      @knowledge = initial_knowledge
      @connections = []
      @info = {}
    end
    
    def add_info(key, value)
      @info[key] = value
      @knowledge = [@knowledge + 0.1, 1.0].min
    end
    
    def get(key)
      @info[key]
    end
    
    def has?(key)
      @info.key?(key)
    end
    
    def merge(key, value)
      existing = @info[key]
      if existing.nil?
        add_info(key, value)
      elsif existing != value
        @info[key] = [existing, value].flatten.uniq
        @knowledge = [@knowledge + 0.05, 1.0].min
      end
    end
    
    def connect_to(other)
      @connections << other unless @connections.include?(other)
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # GAME: Main game engine
  # ═══════════════════════════════════════════════════════════════
  
  class Game
    attr_reader :worlds, :beads, :connections, :moves, :score, :current_world
    
    def initialize(seed: 1069)
      @seed = seed
      @rng = SplitMixTernary.new(seed)
      @worlds = []
      @beads = []
      @connections = []  # [bead1, bead2, via]
      @moves = []
      @score = 0
      @propagator_cells = {}
      
      # Initialize starting world
      @current_world = PossibleWorld.new(seed: seed)
      @worlds << @current_world
    end
    
    def add_bead(bead)
      @beads << bead unless @beads.include?(bead)
      @current_world.add_bead(bead)
      
      # Create propagator cell for domain
      @propagator_cells[bead.domain] ||= PropagatorCell.new(bead.domain)
      @propagator_cells[bead.domain].add_info(bead.concept, bead.metadata)
      
      bead
    end
    
    def add_connection(bead1, bead2, via)
      @connections << [bead1, bead2, via]
      
      # Connect propagator cells
      cell1 = @propagator_cells[bead1.domain]
      cell2 = @propagator_cells[bead2.domain]
      cell1&.connect_to(cell2) if cell2
      cell2&.connect_to(cell1) if cell1
    end
    
    def add_world(world)
      @worlds << world unless @worlds.any? { |w| w.seed == world.seed }
    end
    
    def transpose_structure(structure, from_domain, to_domain, functor)
      source_beads = @beads.select { |b| b.domain == from_domain }
      source_beads.each do |bead|
        new_bead = Bead.new(to_domain, "#{functor}(#{bead.concept})", 
                           seed: bead.seed ^ functor.hash)
        add_bead(new_bead)
        add_connection(bead, new_bead, functor)
      end
    end
    
    def execute_move!(move)
      result = move.execute!(self)
      return nil unless result
      
      points = move.points
      @score += points
      @moves << { move: move.class.name, points: points, timestamp: Time.now.to_f }
      
      { result: result, points: points, total_score: @score }
    end
    
    def hop_to!(target_world)
      path_result = BadiouTriangle.shortest_path(@current_world, target_world, @worlds)
      return nil if path_result[:distance] == Float::INFINITY
      
      # Execute hops along path
      path_result[:path].each_cons(2) do |from, to|
        event = Event.new(site: [:polarity], name: "hop_#{from.seed}_#{to.seed}")
        @current_world = to
      end
      
      path_result
    end
    
    # Run epistemic arbitrage
    def arbitrage!
      gains = []
      
      @propagator_cells.values.combination(2).each do |cell1, cell2|
        # Transfer knowledge from higher to lower
        if cell1.knowledge > cell2.knowledge
          diff = cell1.knowledge - cell2.knowledge
          cell1.connections.each do |connected|
            if connected == cell2
              cell2.merge(:transferred_from, cell1.domain)
              gains << { from: cell1.domain, to: cell2.domain, gain: diff }
            end
          end
        end
      end
      
      gains
    end
    
    def to_h
      {
        seed: @seed,
        score: @score,
        worlds: @worlds.map(&:to_h),
        beads: @beads.map(&:to_h),
        connections: @connections.map { |b1, b2, via| [b1.to_s, b2.to_s, via] },
        moves: @moves
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # MAIN ENTRY POINTS
  # ═══════════════════════════════════════════════════════════════
  
  def self.new_game(seed: 1069)
    Game.new(seed: seed)
  end
  
  def self.from_broadcast(tripartite_system)
    game = Game.new(seed: tripartite_system.agents.first.profile[:seed])
    
    tripartite_system.agents.each do |agent|
      profile = agent.profile
      bead = Bead.new(
        profile[:domain],
        profile[:name],
        seed: profile[:seed],
        metadata: { operations: profile[:operations], polarity: profile[:polarity] }
      )
      game.add_bead(bead)
    end
    
    game
  end
  
  def self.demo(steps: 10, verbose: true)
    puts "╔═══════════════════════════════════════════════════════════════════════════════╗" if verbose
    puts "║  GLASS BEAD GAME: Topos of Music                                              ║" if verbose
    puts "╚═══════════════════════════════════════════════════════════════════════════════╝" if verbose
    puts if verbose
    
    game = new_game
    
    # Add initial beads
    [
      [:mathematics, :prime_numbers, { structure: :multiplicative }],
      [:music, :circle_of_fifths, { structure: :cyclic_12 }],
      [:philosophy, :unity_of_opposites, { dialectic: true }],
      [:physics, :harmonic_oscillator, { equation: :wave }]
    ].each do |domain, concept, meta|
      game.add_bead(Bead.new(domain, concept, metadata: meta))
    end
    
    if verbose
      puts "Initial beads:"
      game.beads.each { |b| puts "  #{b}" }
      puts
    end
    
    # Execute some moves
    moves = [
      Move::Connect.new(
        from: game.beads[0], to: game.beads[1],
        via: :modular_arithmetic
      ),
      Move::Connect.new(
        from: game.beads[1], to: game.beads[3],
        via: :fourier_transform
      ),
      Move::Hop.new(
        from_world: game.current_world,
        event: "Modulation",
        truth_preserved: :harmonic_structure
      )
    ]
    
    moves.each do |move|
      result = game.execute_move!(move)
      if verbose && result
        puts "Move: #{move.class.name.split('::').last}"
        puts "  Points: #{result[:points]}"
        puts "  Total: #{result[:total_score]}"
        puts
      end
    end
    
    # Run arbitrage
    gains = game.arbitrage!
    if verbose && gains.any?
      puts "Epistemic Arbitrage:"
      gains.each { |g| puts "  #{g[:from]} → #{g[:to]}: +#{g[:gain].round(2)}" }
      puts
    end
    
    if verbose
      puts "─" * 80
      puts "Final Score: #{game.score}"
      puts "Worlds: #{game.worlds.size}"
      puts "Beads: #{game.beads.size}"
      puts "Connections: #{game.connections.size}"
    end
    
    game
  end
  
  # MCP Server placeholder
  def self.serve_mcp
    puts "Glass Bead Game MCP Server starting..."
    # TODO: Implement MCP protocol
    loop { sleep 1 }
  end
end

if __FILE__ == $0
  GlassBeadGame.demo
end
