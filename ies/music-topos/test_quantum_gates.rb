#!/usr/bin/env ruby
# test_quantum_gates.rb
# Test suite for Bidirectional Skill Traversal quantum gates

require_relative 'lib/bidirectional_skill_traversal'

puts "=" * 70
puts "TEST: Bidirectional Skill Traversal - Quantum Gates"
puts "=" * 70
puts ""

tests_passed = 0
tests_total = 0

# Test 1: AND gate with high inputs
tests_total += 1
begin
  gate = BidirectionalSkillTraversal::JosephsonJunction.new(gate_type: :and)
  result = gate.apply(0.8, 0.6)  # Both > 0.5, converts to 1 & 1 = 1

  if result == 1
    puts "✓ TEST 1 PASS: AND gate (0.8, 0.6) = 1"
    tests_passed += 1
  else
    puts "✗ TEST 1 FAIL: AND gate returned #{result}, expected 1"
  end
rescue => e
  puts "✗ TEST 1 ERROR: #{e.message}"
end

# Test 2: AND gate with mixed inputs
tests_total += 1
begin
  gate = BidirectionalSkillTraversal::JosephsonJunction.new(gate_type: :and)
  result = gate.apply(0.8, 0.3)  # 0.8 > 0.5 = 1, 0.3 < 0.5 = 0 → 1 & 0 = 0

  if result == 0
    puts "✓ TEST 2 PASS: AND gate (0.8, 0.3) = 0"
    tests_passed += 1
  else
    puts "✗ TEST 2 FAIL: AND gate returned #{result}, expected 0"
  end
rescue => e
  puts "✗ TEST 2 ERROR: #{e.message}"
end

# Test 3: NOT gate
tests_total += 1
begin
  gate = BidirectionalSkillTraversal::JosephsonJunction.new(gate_type: :not)
  result = gate.apply(0.3, nil)  # 0.3 < 0.5 = 0 → NOT 0 = 1

  if result == 1
    puts "✓ TEST 3 PASS: NOT gate (0.3) = 1"
    tests_passed += 1
  else
    puts "✗ TEST 3 FAIL: NOT gate returned #{result}, expected 1"
  end
rescue => e
  puts "✗ TEST 3 ERROR: #{e.message}"
end

# Test 4: XOR gate
tests_total += 1
begin
  gate = BidirectionalSkillTraversal::JosephsonJunction.new(gate_type: :xor)
  result = gate.apply(0.8, 0.3)  # 1 XOR 0 = 1

  if result == 1
    puts "✓ TEST 4 PASS: XOR gate (0.8, 0.3) = 1"
    tests_passed += 1
  else
    puts "✗ TEST 4 FAIL: XOR gate returned #{result}, expected 1"
  end
rescue => e
  puts "✗ TEST 4 ERROR: #{e.message}"
end

# Test 5: OR gate
tests_total += 1
begin
  gate = BidirectionalSkillTraversal::JosephsonJunction.new(gate_type: :or)
  result = gate.apply(0.3, 0.3)  # 0 OR 0 = 0

  if result == 0
    puts "✓ TEST 5 PASS: OR gate (0.3, 0.3) = 0"
    tests_passed += 1
  else
    puts "✗ TEST 5 FAIL: OR gate returned #{result}, expected 0"
  end
rescue => e
  puts "✗ TEST 5 ERROR: #{e.message}"
end

puts ""
puts "=" * 70
puts "RESULTS: #{tests_passed}/#{tests_total} tests passed"
puts "=" * 70

exit tests_passed == tests_total ? 0 : 1
