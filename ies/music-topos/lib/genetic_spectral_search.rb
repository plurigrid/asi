# lib/genetic_spectral_search.rb
# Genetic Search for Seeds with Optimal Spectral Gap Convergence

require_relative 'splitmix_ternary'

module GeneticSpectralSearch
  GOLDEN = 0x9E3779B97F4A7C15
  MASK64 = 0xFFFFFFFFFFFFFFFF
  TARGET_GAP = 0.25  # λ = 1/4
  
  # Fitness: how close to spectral gap 1/4
  def self.fitness(seed, n_steps = 100)
    states = []
    state = seed
    
    n_steps.times do |step|
      gen = SplitMixTernary::Generator.new((seed + step * GOLDEN) & MASK64)
      delta = gen.next_u64
      state = (state ^ delta) & MASK64
      states << state
    end
    
    # Measure mixing via entropy of bit distributions
    bit_counts = Array.new(64, 0)
    states.each { |s| 64.times { |b| bit_counts[b] += (s >> b) & 1 } }
    
    deviations = bit_counts.map { |c| ((c.to_f / n_steps) - 0.5).abs }
    max_deviation = deviations.max
    estimated_gap = [1 - 4 * max_deviation, 0].max
    
    # Fitness = 1 / (1 + |gap - 0.25|)
    1.0 / (1 + (estimated_gap - TARGET_GAP).abs * 10)
  end
  
  # Mutate seed via XOR with random offset
  def self.mutate(seed, mutation_rate = 0.1)
    if rand < mutation_rate
      offset = rand(0..MASK64)
      (seed ^ offset) & MASK64
    else
      seed
    end
  end
  
  # Crossover two seeds via XOR
  def self.crossover(seed1, seed2)
    mask = rand(0..MASK64)
    ((seed1 & mask) | (seed2 & ~mask)) & MASK64
  end
  
  # Selection: tournament
  def self.select(population, fitnesses, tournament_size = 3)
    candidates = population.sample(tournament_size)
    candidate_fits = candidates.map { |c| fitnesses[population.index(c)] }
    candidates[candidate_fits.index(candidate_fits.max)]
  end
  
  # Run genetic search
  def self.search(pop_size: 20, generations: 10, seed: 0x42D)
    # Initialize population
    population = pop_size.times.map { |i| (seed + i * GOLDEN) & MASK64 }
    
    best_ever = nil
    best_fitness = 0
    
    generations.times do |gen|
      fitnesses = population.map { |s| fitness(s) }
      
      # Track best
      gen_best_idx = fitnesses.index(fitnesses.max)
      if fitnesses[gen_best_idx] > best_fitness
        best_fitness = fitnesses[gen_best_idx]
        best_ever = population[gen_best_idx]
      end
      
      # GF(3) trit for this generation
      trit = (gen % 3) - 1
      
      puts "Gen #{gen}: best_fit=#{fitnesses.max.round(4)} avg=#{(fitnesses.sum/fitnesses.size).round(4)} trit=#{trit}"
      
      # Create next generation
      next_pop = [population[gen_best_idx]]  # Elitism
      while next_pop.size < pop_size
        p1 = select(population, fitnesses)
        p2 = select(population, fitnesses)
        child = crossover(p1, p2)
        child = mutate(child)
        next_pop << child
      end
      population = next_pop
    end
    
    { best_seed: best_ever, best_fitness: best_fitness, hex: "0x#{best_ever.to_s(16)}" }
  end
  
  def self.demo
    puts "═══════════════════════════════════════════════════════════════"
    puts "  GENETIC SPECTRAL SEARCH (Subagent ERGODIC, trit=0)"
    puts "═══════════════════════════════════════════════════════════════"
    puts
    result = search(pop_size: 15, generations: 12)
    puts
    puts "Best seed found: #{result[:hex]}"
    puts "Best fitness: #{result[:best_fitness].round(4)}"
  end
end

if __FILE__ == $0
  GeneticSpectralSearch.demo
end
