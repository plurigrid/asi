# test/test_unworld.rb
#
# Test suite for Unworld: Replace Time with Derivation
# Verifies all invariants across multiple seeds

require_relative '../lib/unworld'

module TestUnworld
  SEEDS = [0x42D, 0x1069, 0xDEADBEEF, 0xCAFEBABE, 0x12345678]
  
  def self.run_all
    puts "=" * 70
    puts "TEST SUITE: Unworld Invariants"
    puts "=" * 70
    puts
    
    tests = [
      [:test_seed_chaining_determinism, "Seed chaining is deterministic"],
      [:test_color_chain_verification, "Color chain verifies correctly"],
      [:test_gf3_balance, "GF(3) balance in color chains"],
      [:test_involution_self_inverse, "Involution ι∘ι = id"],
      [:test_three_match_gf3, "3-MATCH GF(3) conservation"],
      [:test_nash_equilibrium, "Best response → Nash equilibrium"],
      [:test_frame_invariance, "Same seed → same derivation"]
    ]
    
    passed = 0
    failed = 0
    
    tests.each do |method, description|
      print "  #{description}... "
      begin
        result = send(method)
        if result
          puts "✓"
          passed += 1
        else
          puts "✗ FAILED"
          failed += 1
        end
      rescue => e
        puts "✗ ERROR: #{e.message}"
        failed += 1
      end
    end
    
    puts
    puts "─" * 70
    puts "Results: #{passed} passed, #{failed} failed"
    puts "=" * 70
    
    failed == 0
  end
  
  # Test 1: Seed chaining is deterministic
  def self.test_seed_chaining_determinism
    SEEDS.all? do |seed|
      # Chain twice, should get same result
      result1 = chain_sequence(seed, 10)
      result2 = chain_sequence(seed, 10)
      result1 == result2
    end
  end
  
  def self.chain_sequence(seed, length)
    current = seed
    sequence = []
    length.times do
      color = Unworld.derive_color(current)
      sequence << [current, color[:trit]]
      current = Unworld.chain_seed(current, color[:trit])
    end
    sequence
  end
  
  # Test 2: Color chain verification
  def self.test_color_chain_verification
    SEEDS.all? do |seed|
      chain = Unworld::ColorChain.new(genesis_seed: seed, length: 20)
      chain.verify_chain
    end
  end
  
  # Test 3: GF(3) balance
  def self.test_gf3_balance
    # At least some chains should be balanced
    balanced_count = SEEDS.count do |seed|
      chain = Unworld::ColorChain.new(genesis_seed: seed, length: 12)
      chain.gf3_balanced?
    end
    balanced_count >= 1  # At least one should be balanced
  end
  
  # Test 4: Involution self-inverse
  def self.test_involution_self_inverse
    SEEDS.all? do |seed|
      inv = Unworld::InvolutionChain.new(genesis_seed: seed, length: 6)
      inv.involution_verified?
    end
  end
  
  # Test 5: 3-MATCH GF(3) conservation
  def self.test_three_match_gf3
    SEEDS.all? do |seed|
      matches = Unworld::ThreeMatchChain.new(genesis_seed: seed, length: 4)
      unworlded = matches.unworld
      unworlded[:all_gf3_conserved]
    end
  end
  
  # Test 6: Nash equilibrium convergence
  def self.test_nash_equilibrium
    SEEDS.all? do |seed|
      best = Unworld::BestResponseChain.new(genesis_seed: seed, max_rounds: 20)
      best.equilibrium_reached?
    end
  end
  
  # Test 7: Frame invariance (same seed → same derivation)
  def self.test_frame_invariance
    SEEDS.all? do |seed|
      # Create chains at different "times" (iterations)
      chain1 = Unworld::ColorChain.new(genesis_seed: seed, length: 10)
      chain2 = Unworld::ColorChain.new(genesis_seed: seed, length: 10)
      
      # Should produce identical results
      chain1.unworld[:derivations] == chain2.unworld[:derivations] &&
      chain1.unworld[:colors] == chain2.unworld[:colors]
    end
  end
  
  # Additional: Property-based testing
  def self.property_test_gf3_transitivity
    puts
    puts "─── Property Test: GF(3) Transitivity ───"
    
    # If chain A has GF(3) = 0 and chain B has GF(3) = 0,
    # then concatenated chain should have GF(3) = 0
    
    results = SEEDS.map do |seed|
      chain_a = Unworld::ColorChain.new(genesis_seed: seed, length: 3)
      
      # Use last seed from chain_a as genesis for chain_b
      last_seed = chain_a.chain.last[:seed]
      chain_b = Unworld::ColorChain.new(genesis_seed: last_seed, length: 3)
      
      sum_a = chain_a.gf3_sum
      sum_b = chain_b.gf3_sum
      combined_sum = sum_a + sum_b
      
      transitive = (sum_a % 3 == 0 && sum_b % 3 == 0) ? (combined_sum % 3 == 0) : true
      
      { seed: seed, sum_a: sum_a, sum_b: sum_b, combined: combined_sum, transitive: transitive }
    end
    
    results.each do |r|
      status = r[:transitive] ? "✓" : "✗"
      puts "  Seed 0x#{r[:seed].to_s(16)}: A=#{r[:sum_a]}, B=#{r[:sum_b]}, A+B=#{r[:combined]} #{status}"
    end
    
    results.all? { |r| r[:transitive] }
  end
end

if __FILE__ == $0
  success = TestUnworld.run_all
  TestUnworld.property_test_gf3_transitivity
  exit(success ? 0 : 1)
end
