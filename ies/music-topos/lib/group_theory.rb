#!/usr/bin/env ruby
# lib/group_theory.rb
#
# Group Theory Implementation for Music Topos
#
# Extends pitch space from cyclic group ℤ/12ℤ to full permutation group S₁₂
# Implements group axioms: closure, associativity, identity, inverse elements
# Uses Cayley graph distance metric that satisfies triangle inequality
#
# Validated against Badiouian ontology for music theory

require_relative 'pitch_class'
require 'set'

# Abstract base class for groups
# A group G is a tuple (G, *, e, inv, metric) where:
# - G is a set of elements
# - * is a binary operation (group multiplication)
# - e is the identity element
# - inv is an inverse function (g → g⁻¹)
# - metric is a distance function satisfying metric axioms
class Group
  attr_reader :elements, :identity, :generators

  def initialize(elements, identity, generators = nil)
    @elements = Set.new(elements)
    @identity = identity
    @generators = generators || []
    @multiplication_table = {}
    @inverse_map = {}
  end

  # Verify group axioms
  # Returns hash: { valid: bool, errors: [String] }
  def validate_group_axioms
    errors = []

    # Axiom 1: Closure - a·b ∈ G for all a,b ∈ G
    sample_size = [@elements.size, 10].min  # Sample for large groups
    elements_sample = @elements.to_a.sample(sample_size)

    errors << "Closure violated: multiplication product not in group" if !check_closure(elements_sample)

    # Axiom 2: Identity - e·a = a·e = a for all a ∈ G
    errors << "Identity axiom violated" if !check_identity(elements_sample)

    # Axiom 3: Inverse - for all a ∈ G, ∃ a⁻¹ ∈ G such that a·a⁻¹ = e
    errors << "Inverse axiom violated" if !check_inverses(elements_sample)

    # Axiom 4: Associativity - (a·b)·c = a·(b·c)
    errors << "Associativity violated" if !check_associativity(elements_sample)

    {
      valid: errors.empty?,
      errors: errors,
      axioms_checked: 4,
      sample_size: sample_size
    }
  end

  # Abstract method - must be implemented by subclasses
  def multiply(a, b)
    raise NotImplementedError, "Subclasses must implement multiply(a, b)"
  end

  # Abstract method
  def inverse(element)
    raise NotImplementedError, "Subclasses must implement inverse(element)"
  end

  # Abstract method
  def distance(element1, element2)
    raise NotImplementedError, "Subclasses must implement distance(element1, element2)"
  end

  protected

  def check_closure(sample)
    sample.each do |a|
      sample.each do |b|
        product = multiply(a, b)
        return false unless @elements.include?(product)
      end
    end
    true
  end

  def check_identity(sample)
    sample.each do |a|
      return false unless multiply(@identity, a) == a
      return false unless multiply(a, @identity) == a
    end
    true
  end

  def check_inverses(sample)
    sample.each do |a|
      inv_a = inverse(a)
      return false if inv_a.nil?
      return false unless @elements.include?(inv_a)
      product = multiply(a, inv_a)
      return false unless product == @identity
    end
    true
  end

  def check_associativity(sample)
    sample.sample([sample.size, 5].min).each do |a|
      sample.sample([sample.size, 5].min).each do |b|
        sample.sample([sample.size, 5].min).each do |c|
          ab_c = multiply(multiply(a, b), c)
          a_bc = multiply(a, multiply(b, c))
          return false unless ab_c == a_bc
        end
      end
    end
    true
  end
end

# Cyclic Group ℤ/nℤ
# Elements: {0, 1, ..., n-1}
# Operation: addition mod n
# Identity: 0
# Inverse of a: n - a (mod n)
class CyclicGroup < Group
  attr_reader :order

  def initialize(n)
    @order = n
    elements = (0...n).to_a
    super(elements, 0, [1])  # Generator is 1
  end

  # Cyclic group multiplication: (a + b) mod n
  def multiply(a, b)
    (a + b) % @order
  end

  # Inverse in cyclic group: -a mod n = (n - a) mod n
  def inverse(a)
    ((@order - a) % @order)
  end

  # Distance in cyclic group: shortest arc on circle
  # min(|a-b|, n - |a-b|)
  def distance(a, b)
    diff = (a - b).abs
    [diff, @order - diff].min
  end

  # Verify triangle inequality
  def triangle_inequality_satisfied?(a, b, c)
    d_ab = distance(a, b)
    d_bc = distance(b, c)
    d_ac = distance(a, c)

    # d(a,c) ≤ d(a,b) + d(b,c)
    d_ac <= d_ab + d_bc + 1e-10
  end
end

# Permutation - represents a bijection of {0, 1, ..., n-1}
# Can be represented as:
# 1. Array: perm[i] = where i goes (one-line notation)
# 2. Cycle notation: (0 1 2) means 0→1, 1→2, 2→0
class Permutation
  attr_reader :mapping, :order

  def initialize(mapping)
    @mapping = mapping.freeze
    @order = mapping.length
  end

  # Create identity permutation
  def self.identity(n)
    Permutation.new((0...n).to_a)
  end

  # Create transposition: swaps two elements
  def self.transposition(n, i, j)
    perm = (0...n).to_a
    perm[i], perm[j] = perm[j], perm[i]
    Permutation.new(perm)
  end

  # Create cycle: (a₀ a₁ ... aₖ)
  # Means a₀ → a₁ → ... → aₖ → a₀
  def self.cycle(n, *cycle_elements)
    perm = (0...n).to_a
    cycle_elements.each_with_index do |elem, idx|
      next_elem = cycle_elements[(idx + 1) % cycle_elements.length]
      perm[elem] = next_elem
    end
    Permutation.new(perm)
  end

  # Compose two permutations: self ∘ other
  # Means: apply other first, then self
  def compose(other)
    raise "Order mismatch" if @order != other.order
    new_mapping = @mapping.map { |i| other.mapping[i] }
    Permutation.new(new_mapping)
  end

  # Inverse: perm⁻¹ such that perm ∘ perm⁻¹ = identity
  def inverse
    inv_mapping = Array.new(@order)
    @mapping.each_with_index do |to, from|
      inv_mapping[to] = from
    end
    Permutation.new(inv_mapping)
  end

  # Apply permutation to array
  def apply_to_array(arr)
    arr.map { |elem| @mapping[elem] }
  end

  # Convert to cycle notation string
  def to_cycles
    visited = Set.new
    cycles = []

    @mapping.each_with_index do |val, idx|
      next if visited.include?(idx)

      cycle = []
      current = idx
      while !visited.include?(current)
        visited.add(current)
        cycle << current
        current = @mapping[current]
      end

      cycles << cycle if cycle.length > 1
    end

    cycles.empty? ? "()" : cycles.map { |c| "(#{c.join(' ')})" }.join
  end

  def to_s
    "Permutation#{to_cycles}"
  end

  def ==(other)
    other.is_a?(Permutation) && @mapping == other.mapping
  end

  def hash
    @mapping.hash
  end
  
  alias_method :eql?, :==
end

# Symmetric Group S_n
# All permutations of n elements
# |S_n| = n!
class SymmetricGroup < Group
  attr_reader :n, :cayley_graph_cache

  def initialize(n)
    @n = n
    @cayley_graph_cache = {}
    identity = Permutation.identity(n)
    super(generate_s_n(n), identity, generate_generators(n))
  end

  # Multiply two permutations: compose them
  def multiply(perm1, perm2)
    perm1.compose(perm2)
  end

  # Inverse of a permutation
  def inverse(perm)
    perm.inverse
  end
  
  # Verify group axioms (overridden for stochastic check on large groups)
  def validate_group_axioms
    # If explicit elements are provided, use base implementation
    return super if @n <= 8
    
    # For implicit symmetric groups (n > 8), we verify axioms stochastically
    errors = []
    
    # Generate a random sample of permutations
    sample_size = 20
    sample = (0...sample_size).map { random_permutation }
    # Ensure identity is in sample
    sample << Permutation.identity(@n)
    
    # Check Closure: product of any two permutations is a valid permutation
    sample.each do |a|
      sample.each do |b|
        prod = multiply(a, b)
        unless prod.is_a?(Permutation) && prod.order == @n
           errors << "Closure violated: product is not a valid permutation"
           return { valid: false, errors: errors }
        end
      end
    end
    
    # Check Identity
    identity = Permutation.identity(@n)
    sample.each do |a|
      unless multiply(identity, a) == a && multiply(a, identity) == a
        errors << "Identity axiom violated"
      end
    end
    
    # Check Inverse
    sample.each do |a|
      inv = inverse(a)
      unless multiply(a, inv) == identity && multiply(inv, a) == identity
        errors << "Inverse axiom violated"
      end
    end
    
    # Check Associativity
    sample.sample(5).each do |a|
      sample.sample(5).each do |b|
        sample.sample(5).each do |c|
           if multiply(multiply(a, b), c) != multiply(a, multiply(b, c))
             errors << "Associativity violated"
           end
        end
      end
    end
    
    {
      valid: errors.empty?,
      errors: errors,
      axioms_checked: 4,
      sample_size: sample.size,
      method: "stochastic"
    }
  end

  def random_permutation
    Permutation.new((0...@n).to_a.shuffle)
  end

  # Cayley graph distance: shortest path using generators as edges
  # BFS from source to target
  def distance(perm1, perm2)
    return 0 if perm1 == perm2

    # Convert to target (perm1⁻¹ · perm2)
    target = perm1.inverse.compose(perm2)

    # BFS for shortest path to target using generators
    queue = [[identity, 0]]
    visited = { identity => 0 }

    while queue.any?
      current, dist = queue.shift
      return dist if current == target

      # Try multiplying by each generator
      @generators.each do |gen|
        next_perm = current.compose(gen)
        unless visited[next_perm]
          visited[next_perm] = dist + 1
          queue.push([next_perm, dist + 1])
        end
      end
    end

    # Should not reach here if target is reachable
    nil
  end

  # Check triangle inequality in Cayley distance
  def triangle_inequality_satisfied?(perm_a, perm_b, perm_c, tolerance = 1e-10)
    d_ab = distance(perm_a, perm_b)
    d_bc = distance(perm_b, perm_c)
    d_ac = distance(perm_a, perm_c)

    return false if d_ab.nil? || d_bc.nil? || d_ac.nil?

    d_ac <= d_ab + d_bc + tolerance
  end

  private

  # Generate all n! permutations (efficient for small n only)
  def generate_s_n(n)
    if n > 8
      # For large n, return generator set instead (space-efficient)
      # In practice, we work with generators, not full set
      return Set.new([Permutation.identity(n)])
    end

    perms = Set.new
    (0...factorial(n)).each do |idx|
      perms << permutation_from_index(n, idx)
    end
    perms
  end

  # Standard generators for S_n: adjacent transpositions (0 1), (1 2), ..., (n-2 n-1)
  def generate_generators(n)
    gens = []
    (0...n-1).each do |i|
      gens << Permutation.transposition(n, i, i + 1)
    end
    gens
  end

  def factorial(n)
    (1..n).reduce(1, :*)
  end

  # Convert factorial number system index to permutation
  def permutation_from_index(n, idx)
    elements = (0...n).to_a
    perm = []

    (0...n).each do |i|
      fact = factorial(n - i - 1)
      pos = idx / fact
      idx = idx % fact

      perm << elements[pos]
      elements.delete_at(pos)
    end

    Permutation.new(perm)
  end
end

# S₁₂ specifically - symmetric group on 12 pitch classes
class S12 < SymmetricGroup
  def initialize
    super(12)
  end

  # Voice leading under S₁₂ action
  # Apply permutation to chord pitches
  def voice_leading_action(chord, permutation)
    original_pitches = chord.voices.map(&:value)
    new_pitches = permutation.apply_to_array(original_pitches)

    # Reconstruct chord with permuted pitches
    new_voices = new_pitches.map { |pitch| PitchClass.new(pitch) }
    Chord.new(*new_voices)
  end

  # Voice leading distance: sum of individual note movements
  def voice_leading_distance(chord1, chord2)
    pitches1 = chord1.voices.map(&:value)
    pitches2 = chord2.voices.map(&:value)

    raise "Chord size mismatch" if pitches1.length != pitches2.length

    total_distance = 0
    pitches1.each_with_index do |p1, idx|
      p2 = pitches2[idx]
      # Distance on circle: min(|p2-p1|, 12 - |p2-p1|)
      dist = (p2 - p1).abs
      circle_dist = [dist, 12 - dist].min
      total_distance += circle_dist
    end

    total_distance
  end
end
