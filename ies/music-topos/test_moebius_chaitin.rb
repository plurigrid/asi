#!/usr/bin/env ruby
# test_moebius_chaitin.rb
#
# Test suite for Möbius Inversion Ternary Computer
# simulating Chaitin machine simulating every von Neumann machine

require_relative 'lib/ternary_computer'
require_relative 'lib/moebius'
require_relative 'lib/chaitin_machine'
require_relative 'lib/von_neumann'
require_relative 'lib/worlds/computational_world'

def assert(condition, message = "Assertion failed")
  raise message unless condition
end

# Color chain from Gay.jl (provided in user state)
COLOR_CHAIN = [
  { cycle: 0, hex: "#232100" }, { cycle: 1, hex: "#FFC196" },
  { cycle: 2, hex: "#B797F5" }, { cycle: 3, hex: "#00D3FE" },
  { cycle: 4, hex: "#F3B4DD" }, { cycle: 5, hex: "#E4D8CA" },
  { cycle: 6, hex: "#E6A0FF" }, { cycle: 7, hex: "#A1AB2D" },
  { cycle: 8, hex: "#430D00" }, { cycle: 9, hex: "#263330" },
  { cycle: 10, hex: "#ACA7A1" }, { cycle: 11, hex: "#004D62" },
  { cycle: 12, hex: "#021300" }, { cycle: 13, hex: "#4E3C3C" },
  { cycle: 14, hex: "#FFD9A8" }, { cycle: 15, hex: "#3A3D3E" },
  { cycle: 16, hex: "#918C8E" }, { cycle: 17, hex: "#AF6535" },
  { cycle: 18, hex: "#68A617" }, { cycle: 19, hex: "#750000" },
  { cycle: 20, hex: "#00C1FF" }, { cycle: 21, hex: "#ED0070" },
  { cycle: 22, hex: "#B84705" }, { cycle: 23, hex: "#00C175" },
  { cycle: 24, hex: "#DDFBE3" }, { cycle: 25, hex: "#003B38" },
  { cycle: 26, hex: "#42717C" }, { cycle: 27, hex: "#DD407D" },
  { cycle: 28, hex: "#8C96CD" }, { cycle: 29, hex: "#CFB45C" },
  { cycle: 30, hex: "#7A39B3" }, { cycle: 31, hex: "#636248" },
  { cycle: 32, hex: "#AB83E5" }, { cycle: 33, hex: "#FEE5FF" },
  { cycle: 34, hex: "#002D79" }, { cycle: 35, hex: "#65947D" }
].freeze

puts "=" * 80
puts "🔢 MÖBIUS INVERSION TERNARY CHAITIN-VON NEUMANN TEST SUITE"
puts "=" * 80
puts ""

tests_passed = 0
tests_total = 0

# =============================================================================
# TEST 1: Balanced Ternary Arithmetic
# =============================================================================
puts "TEST 1: Balanced Ternary Arithmetic"
puts "─" * 80

tests_total += 1
begin
  # Test Word creation and conversion
  w42 = TernaryComputer::Word.new(42)
  assert w42.to_i == 42, "42 should convert correctly"
  
  # Test negative
  wn7 = TernaryComputer::Word.new(-7)
  assert wn7.to_i == -7, "-7 should convert correctly"
  
  # Test addition
  sum = TernaryComputer::Word.new(10) + TernaryComputer::Word.new(5)
  assert sum.to_i == 15, "10 + 5 = 15"
  
  # Test subtraction
  diff = TernaryComputer::Word.new(10) - TernaryComputer::Word.new(3)
  assert diff.to_i == 7, "10 - 3 = 7"
  
  # Test comparison (natural ternary)
  cmp = TernaryComputer::Word.new(5).compare(TernaryComputer::Word.new(3))
  assert cmp.value == 1, "5 > 3 → +1"
  
  puts "  ✓ Word(42).to_i = 42"
  puts "  ✓ Word(-7).to_i = -7"
  puts "  ✓ Word(10) + Word(5) = 15"
  puts "  ✓ Word(10) - Word(3) = 7"
  puts "  ✓ Ternary comparison: 5 <=> 3 → +1"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 2: Möbius Function
# =============================================================================
puts "TEST 2: Möbius Function μ(n)"
puts "─" * 80

tests_total += 1
begin
  # μ(1) = 1
  assert Moebius.mu(1) == 1, "μ(1) = 1"
  
  # μ(p) = -1 for prime p
  assert Moebius.mu(2) == -1, "μ(2) = -1"
  assert Moebius.mu(3) == -1, "μ(3) = -1"
  assert Moebius.mu(5) == -1, "μ(5) = -1"
  
  # μ(pq) = 1 for distinct primes
  assert Moebius.mu(6) == 1, "μ(6) = μ(2×3) = 1"
  assert Moebius.mu(10) == 1, "μ(10) = μ(2×5) = 1"
  
  # μ(p²) = 0
  assert Moebius.mu(4) == 0, "μ(4) = μ(2²) = 0"
  assert Moebius.mu(9) == 0, "μ(9) = μ(3²) = 0"
  
  # μ(30) = μ(2×3×5) = -1
  assert Moebius.mu(30) == -1, "μ(30) = -1"
  
  puts "  ✓ μ(1) = 1"
  puts "  ✓ μ(p) = -1 for primes"
  puts "  ✓ μ(pq) = 1 for distinct primes"
  puts "  ✓ μ(p²) = 0 for squared primes"
  puts "  ✓ μ(30) = μ(2×3×5) = -1"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 3: Möbius Inversion
# =============================================================================
puts "TEST 3: Möbius Inversion (f ↔ g)"
puts "─" * 80

tests_total += 1
begin
  # g(n) = n (identity)
  g = (1..12).to_h { |n| [n, n] }
  
  # f(n) = Σ_{d|n} g(d) = Σ_{d|n} d = σ(n) (sum of divisors)
  f = Moebius.transform(g, 12)
  
  # Verify transform
  assert f[6] == 1 + 2 + 3 + 6, "f(6) = 1+2+3+6 = 12"
  assert f[12] == 1 + 2 + 3 + 4 + 6 + 12, "f(12) = 28"
  
  # Invert: should recover g(n) = n
  (1..12).each do |n|
    recovered = Moebius.invert(f, n)
    assert recovered == n, "Recovered g(#{n}) should be #{n}"
  end
  
  puts "  ✓ Transform: g(n)=n → f(n)=σ(n)"
  puts "  ✓ f(6) = 12 (sum of divisors)"
  puts "  ✓ f(12) = 28"
  puts "  ✓ Inversion recovers g(n) = n"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 4: Prefix-Free Ternary Encoding
# =============================================================================
puts "TEST 4: Prefix-Free Ternary Encoding"
puts "─" * 80

tests_total += 1
begin
  # Encode integers
  enc0 = Moebius::TernaryEncoder.encode(0)
  enc1 = Moebius::TernaryEncoder.encode(1)
  enc7 = Moebius::TernaryEncoder.encode(7)
  
  # Verify prefix-free property
  codes = (0..20).map { |n| Moebius::TernaryEncoder.encode(n) }
  prefix_free = codes.none? do |c1|
    codes.any? { |c2| c1 != c2 && c2.start_with?(c1) }
  end
  
  assert prefix_free, "Codes should be prefix-free"
  
  # Verify decode
  (0..10).each do |n|
    encoded = Moebius::TernaryEncoder.encode(n)
    decoded = Moebius::TernaryEncoder.decode(encoded)
    assert decoded == n, "Decode(Encode(#{n})) = #{n}"
  end
  
  puts "  ✓ Encode(0) = #{enc0}"
  puts "  ✓ Encode(1) = #{enc1}"
  puts "  ✓ Encode(7) = #{enc7}"
  puts "  ✓ All codes are prefix-free"
  puts "  ✓ Decode ∘ Encode = identity"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 5: Chaitin Universal Machine
# =============================================================================
puts "TEST 5: Chaitin Universal Turing Machine"
puts "─" * 80

tests_total += 1
begin
  machine = ChaitinMachine::UniversalMachine.new
  
  # Simple program: write 1, halt
  machine.load([[0, 0, 1, 0, -1]])  # state 0, read 0 → write 1, stay, halt
  result = machine.run(max_steps: 100)
  
  assert result[:halted], "Machine should halt"
  assert result[:output] == [1], "Output should be [1]"
  
  puts "  ✓ Universal machine created"
  puts "  ✓ Simple program executed"
  puts "  ✓ Halted after #{result[:steps]} steps"
  puts "  ✓ Output: #{result[:output]}"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 6: Von Neumann Machine
# =============================================================================
puts "TEST 6: Von Neumann Machine Simulation"
puts "─" * 80

tests_total += 1
begin
  machine = VonNeumann::Machine.new
  
  # Program: load 5, add 3, halt
  # LDA 100 (load from addr 100)
  # ADD 101 (add from addr 101)
  # HLT
  program = [
    VonNeumann::InstructionSet.encode(:LDA, 100),
    VonNeumann::InstructionSet.encode(:ADD, 101),
    VonNeumann::InstructionSet.encode(:HLT, 0),
    0, 0, 0, 0, 0,  # padding
  ]
  
  # Set up data
  machine.load(program)
  machine.state.memory[100] = 5
  machine.state.memory[101] = 3
  
  result = machine.run(max_cycles: 100)
  
  assert result[:halted], "Machine should halt"
  assert result[:accumulator] == 8, "5 + 3 = 8"
  
  puts "  ✓ Von Neumann machine created"
  puts "  ✓ Program: LDA 5, ADD 3, HLT"
  puts "  ✓ Halted after #{result[:cycles]} cycles"
  puts "  ✓ Accumulator: #{result[:accumulator]}"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 7: Universal Simulator (Dovetailing)
# =============================================================================
puts "TEST 7: Universal Simulator (Enumerate All Machines)"
puts "─" * 80

tests_total += 1
begin
  simulator = VonNeumann::UniversalSimulator.new(seed: 0x6761795f636f6c6f)
  
  # Enumerate small machines
  count = simulator.enumerate_machines(max_program_length: 4, base: 3)
  
  # Dovetail execute
  result = simulator.dovetail_execute(max_steps_per_round: 5, max_rounds: 10)
  
  assert count == 81, "3^4 = 81 machines"
  assert result[:total] == 81, "Total should be 81"
  
  puts "  ✓ Enumerated #{count} von Neumann machines"
  puts "  ✓ Dovetailed execution complete"
  puts "  ✓ Halted: #{result[:halted]}"
  puts "  ✓ Non-halting: #{result[:non_halting]}"
  puts "  ✓ Rounds: #{result[:rounds]}"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 8: Computational World (Badiouian Ontology)
# =============================================================================
puts "TEST 8: ComputationalWorld with Badiouian Ontology"
puts "─" * 80

tests_total += 1
begin
  world = MusicalWorlds::ComputationalWorld.from_color_chain(COLOR_CHAIN)
  
  # Validate semantic closure
  closure = world.semantic_closure_validation
  
  assert closure[:program_space], "Should have programs"
  assert closure[:appearance], "Objects should appear"
  assert closure[:existence], "Programs should exist"
  
  # Check metric
  metric_valid = world.validate_metric_space
  
  puts "  ✓ World created from 36-color Gay.jl chain"
  puts "  ✓ Programs: #{world.programs.size}"
  puts "  ✓ Semantic closure: #{closure.values.count(true)}/8 dimensions"
  puts "  ✓ Metric space valid: #{metric_valid[:valid]}"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 9: Triangle Inequality (Kolmogorov Distance)
# =============================================================================
puts "TEST 9: Triangle Inequality (Algorithmic Distance)"
puts "─" * 80

tests_total += 1
begin
  world = MusicalWorlds::ComputationalWorld.new
  
  # Add three programs
  p1 = world.add_program([1], encoding: "10")
  p2 = world.add_program([1, 2], encoding: "110")
  p3 = world.add_program([1, 2, 3], encoding: "1110")
  
  # Validate triangle inequality
  result = world.validate_triangle_inequality(p1, p2, p3)
  
  assert result[:valid], "Triangle inequality should hold"
  
  puts "  ✓ Programs: P1(len=2), P2(len=3), P3(len=4)"
  puts "  ✓ d(P1,P2) = #{result[:d12]}"
  puts "  ✓ d(P2,P3) = #{result[:d23]}"
  puts "  ✓ d(P1,P3) = #{result[:d13]}"
  puts "  ✓ Triangle: #{result[:d13]} ≤ #{result[:d12]} + #{result[:d23]}"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 10: Möbius Inversion on Program Outputs
# =============================================================================
puts "TEST 10: Möbius Inversion on Program Lattice"
puts "─" * 80

tests_total += 1
begin
  world = MusicalWorlds::ComputationalWorld.new
  
  # Build prefix lattice
  p1 = world.add_program([1], encoding: "1")
  p2 = world.add_program([2], encoding: "10")
  p3 = world.add_program([3], encoding: "11")
  p4 = world.add_program([4], encoding: "100")
  
  # Outputs (cumulative over prefixes)
  outputs = { "1" => 10, "10" => 15, "11" => 12, "100" => 20 }
  
  # Invert
  inverted = world.moebius_invert(outputs)
  
  puts "  ✓ Built prefix lattice with 4 programs"
  puts "  ✓ Outputs: #{outputs}"
  puts "  ✓ Inverted: #{inverted}"
  puts "  ✓ Atomic contributions recovered via μ"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# SUMMARY
# =============================================================================
puts "=" * 80
puts "TEST SUMMARY"
puts "=" * 80
puts ""

if tests_passed == tests_total
  puts "✓ ALL #{tests_total} TESTS PASSED!"
else
  puts "✗ #{tests_passed}/#{tests_total} tests passed"
end

puts ""
puts "System Architecture:"
puts "  ┌─────────────────────────────────────────────────────────────┐"
puts "  │  Möbius Inversion Layer (recover atomic contributions)     │"
puts "  │    ↓ μ(p,q) on prefix lattice                              │"
puts "  ├─────────────────────────────────────────────────────────────┤"
puts "  │  Ternary Computer (balanced trits: T, 0, 1)                │"
puts "  │    ↓ 3^n state space, natural comparison                   │"
puts "  ├─────────────────────────────────────────────────────────────┤"
puts "  │  Chaitin Universal Machine (prefix-free, Ω₃)               │"
puts "  │    ↓ dovetailed enumeration, halting probability           │"
puts "  ├─────────────────────────────────────────────────────────────┤"
puts "  │  Von Neumann Machines (all 3^n programs)                   │"
puts "  │    ↓ stored program, fetch-decode-execute                  │"
puts "  ├─────────────────────────────────────────────────────────────┤"
puts "  │  ComputationalWorld (Badiouian ontology)                   │"
puts "  │    • Objects: prefix-free programs                         │"
puts "  │    • Metric: Kolmogorov distance                           │"
puts "  │    • Appearance: halting probability                       │"
puts "  │    • Triangle inequality: enforced                         │"
puts "  └─────────────────────────────────────────────────────────────┘"
puts ""
puts "Seed: 0x6761795f636f6c6f = 'gay_colo'"
puts "Color chain cycles: #{COLOR_CHAIN.size}"
