# lib/ramanujan_complex.rb
#
# Ramanujan Complex and Random Walks

require 'set'
#
# Ramanujan complexes are high-dimensional expanders with optimal spectral gap.
# They generalize Ramanujan graphs (Lubotzky-Phillips-Sarnak) to simplicial complexes.
#
# Here we build a Ramanujan-like complex from:
# 1. de Paiva's categorical structures (Dialectica, Linear Logic, Modal Logic)
# 2. Ungar game bisimulation on lattice structures
# 3. Möbius inversion harmonies (-1, 0, +1)
#
# Musical application:
# - Vertices = pitch classes / harmonic concepts
# - Edges = voice leading / categorical morphisms
# - Triangles = triads / 2-simplices
# - Random walk = melodic exploration with spectral gap (non-degeneracy)

require_relative 'moebius'

module RamanujanComplex
  # ==========================================================================
  # SIMPLICIAL COMPLEX
  # ==========================================================================
  
  class SimplicialComplex
    attr_reader :vertices, :simplices, :dimension
    
    def initialize
      @vertices = Set.new
      @simplices = Hash.new { |h, k| h[k] = Set.new }  # dim → set of simplices
      @dimension = -1
    end
    
    def add_vertex(v)
      @vertices << v
      @simplices[0] << [v].to_set
      @dimension = [@dimension, 0].max
    end
    
    def add_simplex(vertices)
      vset = vertices.to_set
      dim = vset.size - 1
      return if dim < 0
      
      # Add all faces (downward closure)
      (1..vset.size).each do |k|
        vset.to_a.combination(k).each do |face|
          @simplices[k - 1] << face.to_set
        end
      end
      
      vset.each { |v| @vertices << v }
      @dimension = [@dimension, dim].max
    end
    
    # k-skeleton: all simplices of dimension ≤ k
    def skeleton(k)
      (0..k).flat_map { |d| @simplices[d].to_a }
    end
    
    # Boundary of a k-simplex: (k-1)-simplices
    def boundary(simplex)
      return [] if simplex.size <= 1
      simplex.to_a.map { |v| (simplex - [v].to_set) }
    end
    
    # Coboundary: k-simplices containing this (k-1)-simplex
    def coboundary(simplex)
      dim = simplex.size
      @simplices[dim].select { |s| simplex.subset?(s) }
    end
    
    # f-vector: (f_0, f_1, ..., f_d) counting simplices
    def f_vector
      (0..@dimension).map { |d| @simplices[d].size }
    end
    
    def to_s
      "SimplicialComplex(dim=#{@dimension}, f=#{f_vector})"
    end
  end
  
  # ==========================================================================
  # RAMANUJAN PROPERTY: Spectral Gap
  # ==========================================================================
  
  # Laplacian operator on simplicial complex
  class Laplacian
    attr_reader :complex, :dimension
    
    def initialize(complex, dim)
      @complex = complex
      @dimension = dim
      @simplices = complex.simplices[dim].to_a
      @index = @simplices.each_with_index.to_h
    end
    
    # Upper Laplacian L_up = δ*δ (coboundary ∘ coboundary^*)
    def upper_laplacian_matrix
      n = @simplices.size
      return [[0]] if n == 0
      
      matrix = Array.new(n) { Array.new(n, 0.0) }
      
      @simplices.each_with_index do |s1, i|
        # Diagonal: number of (dim+1)-simplices containing s1
        cofaces = @complex.coboundary(s1)
        matrix[i][i] = cofaces.size.to_f
        
        # Off-diagonal: shared cofaces
        @simplices.each_with_index do |s2, j|
          next if i >= j
          shared = cofaces.count { |cf| s2.subset?(cf) }
          if shared > 0
            matrix[i][j] = -1.0
            matrix[j][i] = -1.0
          end
        end
      end
      
      matrix
    end
    
    # Power iteration for largest eigenvalue
    def spectral_gap(iterations: 100)
      matrix = upper_laplacian_matrix
      n = matrix.size
      return 0.0 if n <= 1
      
      # Find λ_1 and λ_2 (largest and second-largest)
      # Simplified: estimate via power iteration
      v = Array.new(n) { rand - 0.5 }
      v = normalize(v)
      
      lambda_prev = 0.0
      iterations.times do
        w = mat_vec(matrix, v)
        lambda_curr = dot(v, w)
        v = normalize(w)
        lambda_prev = lambda_curr
      end
      
      lambda_1 = lambda_prev
      
      # Spectral gap = λ_1 - λ_2 (approximated)
      # For Ramanujan property: gap should be ≥ 2√(d-1) where d is degree
      lambda_1
    end
    
    private
    
    def normalize(v)
      norm = Math.sqrt(v.sum { |x| x * x })
      norm > 0 ? v.map { |x| x / norm } : v
    end
    
    def dot(u, v)
      u.zip(v).sum { |a, b| a * b }
    end
    
    def mat_vec(m, v)
      m.map { |row| row.zip(v).sum { |a, b| a * b } }
    end
  end
  
  # ==========================================================================
  # DE PAIVA CONCEPTUAL SPACE
  # ==========================================================================
  
  # Vertices from Valeria de Paiva's work
  module DePaivaSpace
    DIALECTICA = {
      objects: [:U, :X, :alpha],  # (U, X, α) where α ⊆ U × X
      morphisms: [:f, :F],        # (f, F): (U,X,α) → (V,Y,β)
      composition: :dialectica_comp,
      identity: :dialectica_id
    }.freeze
    
    LINEAR_LOGIC = {
      connectives: [:tensor, :par, :with, :plus, :bang, :quest, :lollipop],
      polarities: [:positive, :negative],
      rules: [:cut, :identity, :exchange, :contraction, :weakening]
    }.freeze
    
    MODAL_LOGIC = {
      modalities: [:box, :diamond],  # □, ◇
      intuitionistic: true,
      constructive: true,
      axioms: [:K, :T, :S4, :S5]
    }.freeze
    
    CHU_SPACES = {
      structure: [:A, :X, :r],  # (A, X, r) where r: A × X → Σ
      duality: :perp,           # A^⊥ = (X, A, r^op)
      tensor: :chu_tensor,
      internal_hom: :chu_hom
    }.freeze
    
    # All concepts as vertices
    def self.all_concepts
      concepts = []
      
      # Dialectica
      concepts += DIALECTICA[:objects].map { |o| [:dialectica, :object, o] }
      concepts += DIALECTICA[:morphisms].map { |m| [:dialectica, :morphism, m] }
      
      # Linear logic
      concepts += LINEAR_LOGIC[:connectives].map { |c| [:linear, :connective, c] }
      concepts += LINEAR_LOGIC[:polarities].map { |p| [:linear, :polarity, p] }
      concepts += LINEAR_LOGIC[:rules].map { |r| [:linear, :rule, r] }
      
      # Modal logic
      concepts += MODAL_LOGIC[:modalities].map { |m| [:modal, :modality, m] }
      concepts += MODAL_LOGIC[:axioms].map { |a| [:modal, :axiom, a] }
      
      # Chu spaces
      concepts += CHU_SPACES[:structure].map { |s| [:chu, :structure, s] }
      
      concepts
    end
    
    # Edges: relationships between concepts
    def self.relationships
      edges = []
      
      # Dialectica ↔ Linear logic
      edges << [[:dialectica, :object, :alpha], [:linear, :connective, :tensor]]
      edges << [[:dialectica, :morphism, :f], [:linear, :rule, :cut]]
      
      # Linear logic internal
      edges << [[:linear, :connective, :tensor], [:linear, :connective, :par]]
      edges << [[:linear, :connective, :with], [:linear, :connective, :plus]]
      edges << [[:linear, :connective, :bang], [:linear, :connective, :quest]]
      edges << [[:linear, :polarity, :positive], [:linear, :connective, :tensor]]
      edges << [[:linear, :polarity, :negative], [:linear, :connective, :par]]
      
      # Modal ↔ Linear
      edges << [[:modal, :modality, :box], [:linear, :connective, :bang]]
      edges << [[:modal, :modality, :diamond], [:linear, :connective, :quest]]
      
      # Chu ↔ Dialectica
      edges << [[:chu, :structure, :A], [:dialectica, :object, :U]]
      edges << [[:chu, :structure, :X], [:dialectica, :object, :X]]
      edges << [[:chu, :structure, :r], [:dialectica, :object, :alpha]]
      
      edges
    end
    
    # Triangles: three-way coherences
    def self.coherences
      [
        # Dialectica-Linear-Chu triangle
        [[:dialectica, :object, :alpha], [:linear, :connective, :tensor], [:chu, :structure, :r]],
        
        # Polarity-Connective triangles
        [[:linear, :polarity, :positive], [:linear, :connective, :tensor], [:linear, :connective, :plus]],
        [[:linear, :polarity, :negative], [:linear, :connective, :par], [:linear, :connective, :with]],
        
        # Modal-Exponential triangle
        [[:modal, :modality, :box], [:linear, :connective, :bang], [:linear, :rule, :contraction]],
      ]
    end
    
    # Build simplicial complex
    def self.build_complex
      complex = SimplicialComplex.new
      
      # Add vertices
      all_concepts.each { |c| complex.add_vertex(c) }
      
      # Add edges
      relationships.each { |e| complex.add_simplex(e) }
      
      # Add triangles
      coherences.each { |t| complex.add_simplex(t) }
      
      complex
    end
  end
  
  # ==========================================================================
  # RANDOM WALK ON COMPLEX
  # ==========================================================================
  
  class RandomWalk
    attr_reader :complex, :position, :history, :seed
    
    def initialize(complex, seed: 0x42D)
      @complex = complex
      @seed = seed
      @rng = Random.new(seed)
      @position = complex.vertices.to_a.sample(random: @rng)
      @history = [@position]
    end
    
    # Step to adjacent vertex (share an edge)
    def step
      edges = @complex.simplices[1].select { |e| e.include?(@position) }
      return @position if edges.empty?
      
      # Choose random edge
      edge = edges.to_a.sample(random: @rng)
      @position = (edge - [@position].to_set).first
      @history << @position
      @position
    end
    
    # Random walk for n steps
    def walk(n)
      n.times { step }
      @history
    end
    
    # Lazy random walk (with holding probability)
    def lazy_walk(n, holding: 0.5)
      n.times do
        if @rng.rand < holding
          @history << @position
        else
          step
        end
      end
      @history
    end
    
    # Stationary distribution (for regular graph)
    def stationary_distribution
      vertices = @complex.vertices.to_a
      degrees = vertices.map do |v|
        @complex.simplices[1].count { |e| e.include?(v) }
      end
      total = degrees.sum.to_f
      vertices.zip(degrees.map { |d| d / total }).to_h
    end
    
    # Mixing time estimate (time to approach stationary)
    def mixing_time_estimate
      # t_mix ≈ log(n) / gap
      n = @complex.vertices.size
      gap = Laplacian.new(@complex, 0).spectral_gap
      gap > 0 ? (Math.log(n) / gap).ceil : Float::INFINITY
    end
  end
  
  # ==========================================================================
  # UNGAR GAME BISIMULATION
  # ==========================================================================
  
  # Bisimulation game on lattice (Ehrenfeucht-Fraïssé style)
  # Ungar's gyrovector spaces inspire the "curved" lattice structure
  class UngarGame
    attr_reader :lattice, :left_position, :right_position, :round
    
    def initialize(lattice, start_left, start_right)
      @lattice = lattice
      @left_position = start_left
      @right_position = start_right
      @round = 0
      @spoiler_moves = []
      @duplicator_moves = []
    end
    
    # Spoiler chooses a direction in one structure
    def spoiler_move(side, direction)
      @round += 1
      pos = side == :left ? @left_position : @right_position
      
      new_pos = case direction
                when :up then @lattice.up(pos)
                when :down then @lattice.down(pos)
                when :left then @lattice.left_neighbor(pos)
                when :right then @lattice.right_neighbor(pos)
                else pos
                end
      
      if side == :left
        @left_position = new_pos
      else
        @right_position = new_pos
      end
      
      @spoiler_moves << [side, direction, new_pos]
      new_pos
    end
    
    # Duplicator must match in the other structure
    def duplicator_respond(side, new_pos)
      if side == :left
        @left_position = new_pos
      else
        @right_position = new_pos
      end
      
      @duplicator_moves << [side, new_pos]
      bisimilar?
    end
    
    # Check if positions are bisimilar (same lattice level, same structure)
    def bisimilar?
      @lattice.level(@left_position) == @lattice.level(@right_position)
    end
    
    # Duplicator wins if bisimulation maintained for k rounds
    def duplicator_wins?(k)
      @round >= k && bisimilar?
    end
  end
  
  # Musical lattice for bisimulation
  class MusicalLattice
    attr_reader :elements
    
    def initialize
      # Lattice of pitch classes with circle-of-fifths ordering
      @elements = (0..11).to_a
      @cof = [0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5]  # Circle of fifths
      @cof_index = @cof.each_with_index.to_h
    end
    
    def level(pitch)
      @cof_index[pitch % 12]
    end
    
    def up(pitch)
      (pitch + 7) % 12  # Up by fifth
    end
    
    def down(pitch)
      (pitch + 5) % 12  # Down by fifth (= up by fourth)
    end
    
    def left_neighbor(pitch)
      (pitch - 1) % 12  # Chromatic down
    end
    
    def right_neighbor(pitch)
      (pitch + 1) % 12  # Chromatic up
    end
    
    # Meet (greatest lower bound)
    def meet(a, b)
      [@cof_index[a], @cof_index[b]].min.then { |i| @cof[i] }
    end
    
    # Join (least upper bound)
    def join(a, b)
      [@cof_index[a], @cof_index[b]].max.then { |i| @cof[i] }
    end
  end
  
  # ==========================================================================
  # MÖBIUS -1, 0, +1 HARMONIES
  # ==========================================================================
  
  class MoebiusHarmonies
    # Generate harmonic progressions based on μ(n) values
    def initialize(seed: 0x42D)
      @seed = seed
      @rng = Random.new(seed)
    end
    
    # Map Möbius values to musical intervals
    # μ = -1 → descending motion (minor feel)
    # μ = 0  → sustained/pedal (squared prime = repetition)
    # μ = +1 → ascending motion (major feel)
    def moebius_to_interval(n)
      mu = Moebius.mu(n)
      case mu
      when -1 then [-3, -4, -5, -7].sample(random: @rng)  # Descending: m3, M3, P4, P5
      when 0  then 0  # Pedal tone
      when 1  then [3, 4, 5, 7].sample(random: @rng)      # Ascending: m3, M3, P4, P5
      end
    end
    
    # Generate progression from number sequence
    def progression_from_sequence(numbers, start_pitch: 60)
      pitches = [start_pitch]
      
      numbers.each do |n|
        interval = moebius_to_interval(n)
        pitches << pitches.last + interval
      end
      
      pitches
    end
    
    # Harmonic coloring based on μ
    def harmonic_color(n)
      mu = Moebius.mu(n)
      case mu
      when -1 then { hue: 240, mode: :minor, direction: :down }   # Blue
      when 0  then { hue: 120, mode: :pedal, direction: :hold }   # Green
      when 1  then { hue: 0,   mode: :major, direction: :up }     # Red
      end
    end
    
    # Inversion-based counterpoint
    # For melody M, counterpoint C where C[i] = M[i] + μ(i+1) * interval
    def moebius_counterpoint(melody, interval: 7)
      melody.each_with_index.map do |pitch, i|
        mu = Moebius.mu(i + 1)
        pitch + (mu * interval)
      end
    end
    
    # 2TDX: 2-dimensional Möbius transform
    # f(m,n) = Σ_{d|m, e|n} g(d,e)
    # Inverts to g(m,n) = Σ_{d|m, e|n} μ(m/d)μ(n/e)f(d,e)
    def two_dimensional_inversion(f_values, m, n)
      result = 0
      Moebius.divisors(m).each do |d|
        Moebius.divisors(n).each do |e|
          mu_prod = Moebius.mu(m / d) * Moebius.mu(n / e)
          result += mu_prod * (f_values[[d, e]] || 0)
        end
      end
      result
    end
  end
  
  # ==========================================================================
  # INTEGRATED SYSTEM
  # ==========================================================================
  
  class RamanujanMusicalComplex
    attr_reader :depaiva_complex, :walker, :lattice, :harmonies
    
    def initialize(seed: 0x42D)
      @seed = seed
      @depaiva_complex = DePaivaSpace.build_complex
      @walker = RandomWalk.new(@depaiva_complex, seed: seed)
      @lattice = MusicalLattice.new
      @harmonies = MoebiusHarmonies.new(seed: seed)
    end
    
    # Walk through de Paiva space, generating music
    def conceptual_walk(steps: 12)
      path = @walker.walk(steps)
      
      # Map concepts to pitches
      pitches = path.map.with_index do |concept, i|
        concept_to_pitch(concept, i)
      end
      
      {
        concepts: path,
        pitches: pitches,
        intervals: pitches.each_cons(2).map { |a, b| b - a },
        moebius_colors: (1..steps).map { |n| @harmonies.harmonic_color(n) }
      }
    end
    
    # Bisimulation game on pitch lattice
    def play_bisimulation_game(start_left, start_right, rounds: 5)
      game = UngarGame.new(@lattice, start_left, start_right)
      
      results = []
      rounds.times do |r|
        # Spoiler moves in alternating structures
        side = r.even? ? :left : :right
        direction = [:up, :down, :left, :right].sample
        game.spoiler_move(side, direction)
        
        # Duplicator responds
        other_side = side == :left ? :right : :left
        # Simple strategy: try to match level
        target_level = @lattice.level(side == :left ? game.left_position : game.right_position)
        current = other_side == :left ? game.left_position : game.right_position
        
        # Move toward target level
        if @lattice.level(current) < target_level
          game.duplicator_respond(other_side, @lattice.up(current))
        elsif @lattice.level(current) > target_level
          game.duplicator_respond(other_side, @lattice.down(current))
        end
        
        results << {
          round: r + 1,
          left: game.left_position,
          right: game.right_position,
          bisimilar: game.bisimilar?
        }
      end
      
      {
        game_results: results,
        winner: game.duplicator_wins?(rounds) ? :duplicator : :spoiler
      }
    end
    
    # Generate Möbius-colored progression
    def moebius_progression(length: 8, start: 60)
      numbers = (1..length).to_a
      @harmonies.progression_from_sequence(numbers, start_pitch: start)
    end
    
    # 2TDX exploration: 2D lattice of harmonies
    def two_dimensional_exploration(m_max: 4, n_max: 4)
      grid = {}
      
      (1..m_max).each do |m|
        (1..n_max).each do |n|
          mu_m = Moebius.mu(m)
          mu_n = Moebius.mu(n)
          product = mu_m * mu_n
          
          # Map to interval
          interval = case product
                     when -1 then -7  # Descending fifth
                     when 0  then 0   # Unison
                     when 1  then 7   # Ascending fifth
                     end
          
          grid[[m, n]] = {
            mu_m: mu_m,
            mu_n: mu_n,
            product: product,
            interval: interval,
            pitch: 60 + (m - 1) * 4 + interval
          }
        end
      end
      
      grid
    end
    
    # Spectral analysis
    def spectral_gap
      Laplacian.new(@depaiva_complex, 0).spectral_gap
    end
    
    private
    
    def concept_to_pitch(concept, index)
      # Map concept categories to pitch regions
      category, type, name = concept
      
      base = case category
             when :dialectica then 60  # C4
             when :linear then 64      # E4
             when :modal then 67       # G4
             when :chu then 72         # C5
             else 60
             end
      
      # Add variation based on specific concept
      offset = name.to_s.bytes.sum % 12
      
      # Add Möbius coloring
      mu_offset = Moebius.mu(index + 1) * 2
      
      base + offset + mu_offset
    end
  end
end
