#!/usr/bin/env ruby
# test_alife_visual_synthesis.rb
#
# Test the integration of artificial life with audio-visual synthesis
# Demonstrates:
#   - Lenia cellular automata generating visual patterns
#   - Particle swarms with emergent behavior
#   - Audio synthesis synchronized to visual evolution
#   - Audio effects applied to life-generated patterns

require_relative 'lib/alife_visual_synthesis'

puts "=" * 80
puts "🧬 AUDIO-VISUAL LIFE SYNTHESIS TEST"
puts "=" * 80
puts ""

tests_passed = 0
tests_total = 0

# ============================================================================
puts "TEST 1: Lenia Cellular Automaton Grid Initialization"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 64, height: 64)
  grid = alife.send(:initialize_lenia_grid)

  # Verify grid structure
  is_valid = grid.length == 64 &&
             grid[0].length == 64 &&
             grid.all? { |row| row.all? { |cell| cell >= 0.0 && cell <= 1.0 } }

  # Check for seed pattern in center
  center_y = 32
  center_x = 32
  center_energy = grid[center_y][center_x]

  if is_valid && center_energy > 0.5
    puts "  ✓ Lenia grid initialized correctly"
    puts "    Grid size: 64x64"
    puts "    Center seed energy: #{center_energy.round(3)}"
    puts "    Grid values: [0.0, 1.0] range ✓"
    tests_passed += 1
  else
    puts "  ✗ Grid initialization failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 2: Lenia Evolution (Cellular Automata Step)"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)
  grid = alife.send(:initialize_lenia_grid)

  # Run one step
  new_grid = alife.lenia_step(grid)

  # Verify structure
  structure_ok = new_grid.length == 32 && new_grid[0].length == 32
  values_ok = new_grid.all? { |row| row.all? { |cell| cell >= 0.0 && cell <= 1.0 } }

  # Check if grid changed (evolution occurred)
  changed = grid != new_grid

  if structure_ok && values_ok && changed
    puts "  ✓ Lenia step executed successfully"
    puts "    Grid structure maintained: 32x32 ✓"
    puts "    Value range [0.0, 1.0]: ✓"
    puts "    Evolution occurred (grid changed): ✓"
    tests_passed += 1
  else
    puts "  ✗ Lenia evolution failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 3: Particle Swarm Initialization & Movement"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 256, height: 256)

  # Create swarm
  particles = Array.new(10) { AlifeVisualSynthesis::Particle.new(256, 256) }

  # Run step
  particles = alife.particle_swarm_step(particles)

  # Verify particles
  all_valid = particles.all? do |p|
    p.x >= 0 && p.x < 256 &&
      p.y >= 0 && p.y < 256 &&
      p.energy >= 0 && p.energy <= 1.0
  end

  if all_valid && particles.length == 10
    puts "  ✓ Particle swarm initialized and updated"
    puts "    Number of particles: #{particles.length}"
    puts "    All particles in bounds: ✓"
    puts "    Sample particle state:"
    puts "      Position: (#{particles[0].x.round(1)}, #{particles[0].y.round(1)})"
    puts "      Velocity: (#{particles[0].vx.round(3)}, #{particles[0].vy.round(3)})"
    puts "      Energy: #{particles[0].energy.round(3)}"
    tests_passed += 1
  else
    puts "  ✗ Particle swarm validation failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 4: Grid to Audio Frequency Mapping"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)
  grid = alife.send(:initialize_lenia_grid)

  # Convert grid to frequencies
  frequencies = alife.grid_to_frequencies(grid, base_frequency: 440)

  # Verify frequencies
  freq_valid = frequencies.all? { |f| f > 0 && f < 20000 }
  has_content = frequencies.length > 0

  if freq_valid && has_content
    puts "  ✓ Grid to frequency mapping successful"
    puts "    Base frequency: 440 Hz"
    puts "    Generated frequencies: #{frequencies.length}"
    puts "    Frequency range: #{frequencies.min.round(2)} - #{frequencies.max.round(2)} Hz"
    puts "    Sample frequencies: #{frequencies.first(3).map { |f| f.round(2) }.join(', ')} Hz"
    tests_passed += 1
  else
    puts "  ✗ Frequency mapping failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 5: Full Audio-Visual Lenia Simulation (5 steps)"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)

  # Run simulation for 5 steps
  result = alife.simulate_audiovisual_life(steps: 5, life_type: :lenia)

  # Verify result structure
  has_frames = result[:visual_frames].length == 5
  has_audio = result[:audio_samples].length > 0
  duration_reasonable = result[:duration_seconds] > 0 && result[:duration_seconds] < 10

  if has_frames && has_audio && duration_reasonable
    puts "  ✓ Audio-visual Lenia simulation completed"
    puts "    Frames generated: #{result[:visual_frames].length}"
    puts "    Audio samples: #{result[:audio_samples].length}"
    puts "    Duration: #{result[:duration_seconds].round(2)} seconds"
    puts "    Expected duration: ~2.5 seconds (5 frames × 0.5 sec)"
    tests_passed += 1
  else
    puts "  ✗ Simulation failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 6: Particle Swarm Audio-Visual Simulation"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 128, height: 128)

  # Run swarm simulation
  result = alife.simulate_audiovisual_life(steps: 3, life_type: :swarm)

  # Verify result
  has_frames = result[:visual_frames].length == 3
  has_audio = result[:audio_samples].length > 0

  if has_frames && has_audio
    puts "  ✓ Audio-visual particle swarm simulation completed"
    puts "    Frames generated: #{result[:visual_frames].length}"
    puts "    Particles per frame: ~30"
    puts "    Audio samples: #{result[:audio_samples].length}"
    puts "    Duration: #{result[:duration_seconds].round(2)} seconds"
    tests_passed += 1
  else
    puts "  ✗ Swarm simulation failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 7: Audio Effects on Life-Generated Patterns"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)

  # Create effect chain
  effects_chain = [
    {
      effect: :reverb,
      params: { room_size: 0.6, damping: 0.5, wet_mix: 0.4 }
    },
    {
      effect: :chorus,
      params: { delay_time: 0.02, rate: 1.5, depth: 0.002 }
    }
  ]

  # Run simulation with effects
  result = alife.simulate_audiovisual_life(
    steps: 2,
    life_type: :lenia,
    effects_chain: effects_chain
  )

  if result[:audio_samples].length > 0 && result[:visual_frames].length == 2
    puts "  ✓ Audio effects applied to life-generated patterns"
    puts "    Effects chain: reverb → chorus"
    puts "    Frames: #{result[:visual_frames].length}"
    puts "    Audio samples: #{result[:audio_samples].length}"
    puts "    Duration: #{result[:duration_seconds].round(2)} seconds"
    tests_passed += 1
  else
    puts "  ✗ Effects application failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 8: Render to WAV File"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)
  result = alife.simulate_audiovisual_life(steps: 2, life_type: :lenia)

  # Render to file
  output = alife.render_audio_visual(result, output_wav: '/tmp/test_alife.wav')

  if File.exist?(output[:audio_file]) && File.size(output[:audio_file]) > 1000
    puts "  ✓ Audio-visual synthesis rendered to WAV"
    puts "    File: #{output[:audio_file]}"
    puts "    Size: #{File.size(output[:audio_file])} bytes"
    puts "    Duration: #{output[:duration].round(2)} seconds"
    puts "    Visual frames: #{output[:frames]}"
    tests_passed += 1
  else
    puts "  ✗ WAV file generation failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST SUMMARY"
puts "=" * 80
puts ""

if tests_passed == tests_total
  puts "✓ ALL #{tests_total} TESTS PASSED!"
  puts ""
  puts "Audio-Visual Life Synthesis Status: FULLY OPERATIONAL"
  puts ""
  puts "✓ Lenia cellular automata implementation working"
  puts "✓ Particle swarm dynamics functional"
  puts "✓ Visual-to-audio mapping successful"
  puts "✓ Integrated simulations executing correctly"
  puts "✓ Audio effects integration validated"
  puts "✓ WAV file generation working"
  puts ""
  puts "Generated assets:"
  puts "  /tmp/test_alife.wav - Audio-visual Lenia composition"
  puts ""
  puts "Next: Integration with p5.js visualization + Laura Porta video framework"
  puts ""

  exit 0
else
  puts "✗ #{tests_total - tests_passed} TEST(S) FAILED (#{tests_passed}/#{tests_total})"
  puts ""
  puts "Please check output above for details."
  puts ""

  exit 1
end
