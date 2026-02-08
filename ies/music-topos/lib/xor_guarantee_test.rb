# lib/xor_guarantee_test.rb
# XOR Guarantee Assessment for Expander Graph Random Walk

require_relative 'splitmix_ternary'

module XORGuarantee
  GOLDEN = 0x9E3779B97F4A7C15
  MASK64 = 0xFFFFFFFFFFFFFFFF
  
  # Test involutory property: walk ⊕ walk = identity
  def self.test_involutory(seed, n_trials = 100)
    failures = 0
    n_trials.times do |trial|
      state = seed ^ (trial * GOLDEN)
      original = state
      
      # Walk forward
      gen = SplitMixTernary::Generator.new(state)
      delta = gen.next_u64
      walked = (state ^ delta) & MASK64
      
      # Walk backward (XOR is its own inverse)
      restored = (walked ^ delta) & MASK64
      
      failures += 1 unless restored == original
    end
    
    { trials: n_trials, failures: failures, success_rate: 1.0 - failures.to_f / n_trials }
  end
  
  # Test spectral gap convergence
  def self.spectral_gap_estimate(seed, n_steps = 1000)
    states = []
    state = seed
    
    n_steps.times do |step|
      gen = SplitMixTernary::Generator.new((seed + step * GOLDEN) & MASK64)
      delta = gen.next_u64
      state = (state ^ delta) & MASK64
      states << state
    end
    
    # Estimate mixing via bit distribution
    bit_counts = Array.new(64, 0)
    states.each do |s|
      64.times { |b| bit_counts[b] += (s >> b) & 1 }
    end
    
    # Ideal: each bit is 1 half the time
    deviations = bit_counts.map { |c| ((c.to_f / n_steps) - 0.5).abs }
    max_deviation = deviations.max
    
    # Spectral gap estimate: λ ≈ 1 - 4*max_deviation (heuristic)
    estimated_gap = [1 - 4 * max_deviation, 0].max
    
    { 
      n_steps: n_steps,
      max_bit_deviation: max_deviation,
      estimated_spectral_gap: estimated_gap,
      target_gap: 0.25,
      converged: (estimated_gap - 0.25).abs < 0.1
    }
  end
  
  def self.demo(seed = 0x42D)
    puts "═══════════════════════════════════════════════════════════════"
    puts "  XOR GUARANTEE ASSESSMENT (Subagent MINUS, trit=-1)"
    puts "═══════════════════════════════════════════════════════════════"
    puts
    puts "Seed: 0x#{seed.to_s(16)}"
    puts
    
    inv = test_involutory(seed)
    puts "─── Involutory Test ───"
    puts "  Trials: #{inv[:trials]}"
    puts "  Failures: #{inv[:failures]}"
    puts "  Success Rate: #{(inv[:success_rate] * 100).round(2)}%"
    puts
    
    spec = spectral_gap_estimate(seed)
    puts "─── Spectral Gap Estimate ───"
    puts "  Steps: #{spec[:n_steps]}"
    puts "  Max Bit Deviation: #{spec[:max_bit_deviation].round(4)}"
    puts "  Estimated Gap: #{spec[:estimated_spectral_gap].round(4)}"
    puts "  Target (1/4): #{spec[:target_gap]}"
    puts "  Converged: #{spec[:converged] ? '✓' : '✗'}"
  end
end

if __FILE__ == $0
  XORGuarantee.demo
end
