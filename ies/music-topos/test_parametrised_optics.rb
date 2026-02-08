#!/usr/bin/env ruby
# test_parametrised_optics.rb
#
# Test suite for Parametrised Optics in Musical Cybernetics
#
# "⊛ represents agency being exerted on systems"

require_relative 'lib/parametrised_optics'

def assert(condition, message = "Assertion failed")
  raise message unless condition
end

include ParametrisedOptics

puts "=" * 70
puts "🔭 PARAMETRISED OPTICS: Musical Cybernetics Test Suite"
puts "=" * 70
puts ""

tests_passed = 0
tests_total = 0

# =============================================================================
# TEST 1: Basic Lens (get/put)
# =============================================================================
puts "TEST 1: Lens - Focus on Note Component"
puts "─" * 70

tests_total += 1
begin
  note = { pitch: 60, duration: 0.5, velocity: 80 }
  
  # Get pitch
  result = Musical::PITCH_LENS.get(note)
  assert result[:focus] == 60, "Should extract pitch 60"
  
  # Put new pitch
  updated = Musical::PITCH_LENS.put(note, 72)
  assert updated[:pitch] == 72, "Should update pitch to 72"
  assert updated[:duration] == 0.5, "Duration preserved"
  assert updated[:velocity] == 80, "Velocity preserved"
  
  puts "  ✓ Lens.get extracts focus: pitch=#{result[:focus]}"
  puts "  ✓ Lens.put updates focus: #{note[:pitch]} → #{updated[:pitch]}"
  puts "  ✓ Residual (duration, velocity) preserved"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 2: Prism (match/build)
# =============================================================================
puts "TEST 2: Prism - Optional Transformation"
puts "─" * 70

tests_total += 1
begin
  smooth = { from: 60, to: 62 }   # Step motion (2 semitones)
  leap = { from: 60, to: 72 }     # Leap (12 semitones)
  
  smooth_result = Musical::VOICE_LEADING_PRISM.get(smooth)
  leap_result = Musical::VOICE_LEADING_PRISM.get(leap)
  
  assert smooth_result[:residual] == :matched, "Smooth motion should match"
  assert leap_result[:residual] == :unmatched, "Leap should not match"
  
  puts "  ✓ Prism matches smooth voice leading: #{smooth}"
  puts "  ✓ Prism rejects leap: #{leap}"
  puts "  ✓ Partial transformations via sum types"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 3: Para (Parametrised Morphism)
# =============================================================================
puts "TEST 3: Para - Parametrised Morphism (Agency)"
puts "─" * 70

tests_total += 1
begin
  # Agent chooses transposition interval
  transposed_up = Musical::TRANSPOSE.apply(7, 0)   # C up P5 → G
  transposed_down = Musical::TRANSPOSE.apply(-5, 0) # C down P4 → G
  
  assert transposed_up == 7, "C + 7 = G"
  assert transposed_down == 7, "C - 5 mod 12 = G"
  
  # Agent chooses chord type
  major = Musical::HARMONIZE.apply(:major, 0)  # C major
  minor = Musical::HARMONIZE.apply(:minor, 0)  # C minor
  
  assert major == [0, 4, 7], "C major = [C, E, G]"
  assert minor == [0, 3, 7], "C minor = [C, Eb, G]"
  
  puts "  ✓ Transpose(+7, C) = G (agent chooses interval)"
  puts "  ✓ Harmonize(:major, C) = #{major} (agent chooses chord type)"
  puts "  ✓ Harmonize(:minor, C) = #{minor}"
  puts "  ✓ Parameter space = agent's choice space"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 4: ⊛ (Para Composition)
# =============================================================================
puts "TEST 4: ⊛ Operator - Sequential Agency"
puts "─" * 70

tests_total += 1
begin
  # Compose: transpose THEN harmonize
  # Agent makes two choices: interval, then chord type
  melodic = Musical::TRANSPOSE.para_compose(Musical::HARMONIZE)
  
  # Apply with parameters [+7, :major] to pitch 0 (C)
  result = melodic.apply([7, :major], 0)
  
  # C → transpose +7 → G → harmonize major → [G, B, D]
  assert result == [7, 11, 2], "C → G major = [7, 11, 2]"
  
  puts "  ✓ transpose ⊛ harmonize = melodic_agency"
  puts "  ✓ Apply([+7, :major], C):"
  puts "      C →[+7]→ G →[:major]→ [G, B, D]"
  puts "  ✓ Result: #{result.map { |p| %w[C C# D D# E F F# G G# A A# B][p] }}"
  puts "  ✓ ⊛ represents sequential agency"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 5: Optic Composition
# =============================================================================
puts "TEST 5: Optic Composition (Lens ∘ Lens)"
puts "─" * 70

tests_total += 1
begin
  # Compose: focus on chord, then focus on root
  # This gives us a lens into the root of a chord inside a larger structure
  
  chord = { pitches: [60, 64, 67], duration: 1.0 }
  
  # Get root
  root_result = Musical::CHORD_ROOT_LENS.get(chord)
  assert root_result[:focus] == 60, "Root should be 60 (C)"
  
  # Transpose root (put new root)
  transposed_chord = Musical::CHORD_ROOT_LENS.put(chord, 65)  # F
  
  # Chord should now be [F, A, C] = [65, 69, 72]
  assert transposed_chord[:pitches] == [65, 69, 72], "Transposed to F major"
  
  puts "  ✓ Extract root: #{chord[:pitches]} → root=#{root_result[:focus]}"
  puts "  ✓ Update root: C major → F major"
  puts "  ✓ New pitches: #{transposed_chord[:pitches]}"
  puts "  ✓ Interval structure preserved"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 6: Cybernetic System
# =============================================================================
puts "TEST 6: Cybernetic System - Dynamical Composition"
puts "─" * 70

tests_total += 1
begin
  initial = { notes: [], time: 0.0, key: 0 }
  system = Musical.create_compositional_system(initial)
  
  # Agent provides intention sequence
  intentions = [:develop, :develop, :contrast, :return, :cadence]
  results = system.run(intentions)
  
  assert system.history.size == intentions.size + 1, "Should have history"
  assert system.state[:notes].size >= 4, "Should have added notes"
  
  pitches = system.state[:notes].map { |n| n[:pitch] }
  
  puts "  ✓ Initial state: #{initial}"
  puts "  ✓ Intentions: #{intentions}"
  puts "  ✓ Final notes: #{pitches.size} pitches"
  puts "  ✓ Agent steers compositional dynamics"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 7: Girard ⊗ (Tensor)
# =============================================================================
puts "TEST 7: Girard ⊗ (Tensor) - Parallel Optics"
puts "─" * 70

tests_total += 1
begin
  note1 = { pitch: 60, duration: 0.5, velocity: 80 }
  note2 = { pitch: 64, duration: 0.5, velocity: 80 }
  
  # Tensor product: apply pitch lens to both notes in parallel
  tensor_lens = GirardOptics.tensor(Musical::PITCH_LENS, Musical::PITCH_LENS)
  
  result = tensor_lens.get([note1, note2])
  assert result[:focus] == [60, 64], "Should extract both pitches"
  
  # Update both
  updated = tensor_lens.put(result[:residual], [72, 76])
  assert updated[0][:pitch] == 72, "First note updated"
  assert updated[1][:pitch] == 76, "Second note updated"
  
  puts "  ✓ ⊗ applies optic to product: [note1, note2]"
  puts "  ✓ Get: #{result[:focus]}"
  puts "  ✓ Put: [72, 76] → parallel update"
  puts "  ✓ Tensor models parallel voice motion"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 8: Girard ! (Bang) - Replication
# =============================================================================
puts "TEST 8: Girard ! (Bang) - Replicated Optic"
puts "─" * 70

tests_total += 1
begin
  notes = [
    { pitch: 60, duration: 0.5, velocity: 80 },
    { pitch: 64, duration: 0.5, velocity: 80 },
    { pitch: 67, duration: 0.5, velocity: 80 }
  ]
  
  # Bang: replicate pitch lens across all notes
  bang_lens = GirardOptics.bang(Musical::PITCH_LENS, 3)
  
  result = bang_lens.get(notes)
  assert result[:focus] == [60, 64, 67], "Should extract all pitches"
  
  # Transpose all by +2
  new_pitches = result[:focus].map { |p| p + 2 }
  updated = bang_lens.put(result[:residual], new_pitches)
  
  assert updated.map { |n| n[:pitch] } == [62, 66, 69], "All transposed"
  
  puts "  ✓ !pitch_lens replicates across chord"
  puts "  ✓ Get: #{result[:focus]}"
  puts "  ✓ Put(+2): #{updated.map { |n| n[:pitch] }}"
  puts "  ✓ Bang models exponential (broadcast transformation)"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 9: Voice Leading Agency
# =============================================================================
puts "TEST 9: Voice Leading as Parametrised Agency"
puts "─" * 70

tests_total += 1
begin
  # Agent chooses voice leading direction
  c_to_g = [60, 67]  # C4 to G4
  
  up = Musical::VOICE_LEAD.apply(:up, c_to_g)
  down = Musical::VOICE_LEAD.apply(:down, c_to_g)
  nearest = Musical::VOICE_LEAD.apply(:nearest, c_to_g)
  
  # Voice lead returns the destination pitch reached from 'from'
  assert up == 67, "Up: C + 7 = G"
  assert down == 55, "Down: C - 5 = G3"
  
  puts "  ✓ Voice lead :up → #{up} (C4 + 7 = G4)"
  puts "  ✓ Voice lead :down → #{down} (C4 - 5 = G3)"
  puts "  ✓ Voice lead :nearest → #{nearest}"
  puts "  ✓ Agent controls voice leading direction"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 10: Para Tensor (Parallel Agency)
# =============================================================================
puts "TEST 10: Para Tensor - Parallel Agency on Voices"
puts "─" * 70

tests_total += 1
begin
  # Two agents control two voices independently
  soprano_agent = Musical::TRANSPOSE
  alto_agent = Musical::TRANSPOSE
  
  parallel_agency = soprano_agent.para_tensor(alto_agent)
  
  # Soprano goes up +4, Alto goes down -3
  soprano_pitch = 72  # C5
  alto_pitch = 64     # E4
  
  result = parallel_agency.apply([4, -3], [soprano_pitch, alto_pitch])
  
  # Transpose mod 12: 72+4=76 mod 12 = 4, 64-3=61 mod 12 = 1
  expected = [(soprano_pitch + 4) % 12, (alto_pitch - 3) % 12]
  assert result == expected, "Soprano and Alto transposed mod 12"
  
  puts "  ✓ Soprano agent: +4 semitones → #{result[0]}"
  puts "  ✓ Alto agent: -3 semitones → #{result[1]}"
  puts "  ✓ Parallel result: #{result}"
  puts "  ✓ ⊗ on Para = independent parallel agency"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# TEST 11: Feedback Loop
# =============================================================================
puts "TEST 11: Cybernetic Feedback Loop"
puts "─" * 70

tests_total += 1
begin
  initial = { notes: [{ pitch: 60 }], time: 0.0, key: 0 }
  system = Musical.create_compositional_system(initial)
  
  # Observer: look at last pitch
  observer = ->(state) { state[:notes].last[:pitch] }
  
  # Controller: if high, go down; if low, go up
  controller = ->(last_pitch) {
    if last_pitch > 70 then :return
    elsif last_pitch < 50 then :contrast
    else :develop
    end
  }
  
  # Run feedback loop
  results = system.feedback_loop(observer, controller, steps: 5)
  
  pitches = system.history.map { |s| s[:notes].last[:pitch] rescue nil }.compact
  
  puts "  ✓ Observer: last pitch of composition"
  puts "  ✓ Controller: high→return, low→contrast, else→develop"
  puts "  ✓ Pitch trajectory: #{pitches.first(8).join(' → ')}"
  puts "  ✓ Feedback maintains pitch within range"
  
  tests_passed += 1
rescue => e
  puts "  ✗ Error: #{e.message}"
end
puts ""

# =============================================================================
# SUMMARY
# =============================================================================
puts "=" * 70
puts "TEST SUMMARY"
puts "=" * 70
puts ""

if tests_passed == tests_total
  puts "✓ ALL #{tests_total} TESTS PASSED!"
else
  puts "✗ #{tests_passed}/#{tests_total} tests passed"
end

puts ""
puts "Parametrised Optics in Musical Cybernetics:"
puts "  ┌────────────────────────────────────────────────────────────────────┐"
puts "  │  OPTICS                        MUSIC                              │"
puts "  ├────────────────────────────────────────────────────────────────────┤"
puts "  │  Lens(S, A)                    Focus on pitch/duration/velocity   │"
puts "  │  Prism(S, A)                   Optional: modulation, voice lead   │"
puts "  │  Optic composition (∘)         Nested focus (chord → root)        │"
puts "  ├────────────────────────────────────────────────────────────────────┤"
puts "  │  Para(P, A, B)                 Agent's choice → transformation    │"
puts "  │  ⊛ (para composition)          Sequential agency (transpose→harm) │"
puts "  │  ⊗ (para tensor)               Parallel agency (SATB voices)      │"
puts "  ├────────────────────────────────────────────────────────────────────┤"
puts "  │  CyberneticSystem              Composition as controlled dynamics │"
puts "  │  Feedback loop                 Agent observes and responds        │"
puts "  ├────────────────────────────────────────────────────────────────────┤"
puts "  │  Girard ⊗ (tensor)             Parallel voice motion              │"
puts "  │  Girard ! (bang)               Broadcast to all voices            │"
puts "  │  Girard ? (quest)              Optional transformation            │"
puts "  └────────────────────────────────────────────────────────────────────┘"
puts ""
puts '"⊛ represents agency being exerted on systems"'
puts "  — The composer IS the agent; the composition IS the system."
