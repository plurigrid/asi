#!/usr/bin/env ruby
#
# demo_phase_5_integration.rb
#
# Comprehensive End-to-End Demo: Learnable Gamut with Musical Interaction
#
# Demonstrates:
# 1. PLR color transformations from Julia (mapped to Ruby)
# 2. Harmonic function analysis of color sequences
# 3. CRDT state merging for distributed agents
# 4. Preference learning loop integration
# 5. Sonic Pi rendering pipeline
#

require_relative 'lib/plr_color_renderer'

puts "\n" + "=" * 80
puts "PHASE 5: Learnable Gamut - End-to-End Integration Demo"
puts "=" * 80
puts

# =========================================================================
# Scenario 1: Single Agent Learning
# =========================================================================

puts "SCENARIO 1: Single Agent Learning"
puts "-" * 80
puts

agent = PLRColorRenderer.new({ H: 0, L: 65, C: 50 })
puts "✓ Agent initialized (C Major)"

# Explore P transformations
puts "\nExplore P (Parallel) transformations:"
3.times do |i|
  result = agent.transform_parallel(1)
  puts "  P(#{i+1}): H=#{result[:color][:H].round(1)}° [#{result[:harmonic_function]}]"
end

analysis1 = agent.analyze_harmonic_progression
puts "\nProgression analysis: #{analysis1[:progression_type]}"
puts "Has all three functions: #{analysis1[:closure][:complete]}"

# =========================================================================
# Scenario 2: Multi-Agent Convergence
# =========================================================================

puts "\n\nSCENARIO 2: Multi-Agent Convergence"
puts "-" * 80
puts

agent1 = PLRColorRenderer.new({ H: 0, L: 65, C: 50 })
agent2 = PLRColorRenderer.new({ H: 120, L: 65, C: 50 })

puts "✓ Agent 1 initialized (H=0°)"
puts "✓ Agent 2 initialized (H=120°)"

# Each agent learns independently
puts "\nAgent 1 explores R transformations:"
2.times { agent1.transform_relative(1) }

puts "Agent 2 explores L transformations:"
2.times { agent2.transform_leading_tone(1) }

puts "\nBefore merge:"
puts "  Agent 1 colors: #{agent1.color_history.length}"
puts "  Agent 2 colors: #{agent2.color_history.length}"

# Merge via CRDT
state1 = agent1.to_h
state2 = agent2.to_h
agent1.merge!(state2)

puts "\nAfter CRDT merge:"
puts "  Agent 1 total colors: #{agent1.color_history.length}"
puts "  Combined history: #{agent1.color_history.map { |c| "H=#{c[:H].round(0)}°" }.join(", ")}"

# =========================================================================
# Scenario 3: Preference Learning
# =========================================================================

puts "\n\nSCENARIO 3: Preference Learning"
puts "-" * 80
puts

learner = PLRColorRenderer.new({ H: 45, L: 65, C: 50 })
puts "✓ Learner initialized"

# Generate color palette
puts "\nGenerating color palette via PLR exploration:"
6.times do |i|
  if i.even?
    learner.transform_parallel((i.even? ? 1 : -1))
  else
    learner.transform_leading_tone((i.even? ? 1 : -1))
  end
end

puts "  Generated #{learner.color_history.length} colors"

# Record binary preferences
puts "\nRecording binary preferences:"
prefs = [
  [0, 1],  # Prefer color 0 to color 1
  [2, 1],  # Prefer color 2 to color 1
  [3, 4]   # Prefer color 3 to color 4
]

prefs.each do |pref_idx, rej_idx|
  pref = learner.record_preference(pref_idx, rej_idx)
  puts "  P[#{pref_idx}] > R[#{rej_idx}] : gradient=#{(pref[:gradient] * 100).round(0)}%"
end

# Analyze learning progress
summary = learner.session_summary
puts "\nLearning summary:"
puts "  Colors explored: #{summary[:colors_generated]}"
puts "  Functions discovered: #{summary[:harmonic_functions]}"
puts "  Preferences recorded: #{summary[:preferences_recorded]}"
puts "  Harmonic closure: #{summary[:progression_type]}"

# =========================================================================
# Scenario 4: Hexatonic Cycle Discovery
# =========================================================================

puts "\n\nSCENARIO 4: Hexatonic Cycle (P-L-P-L-P-L)"
puts "-" * 80
puts

explorer = PLRColorRenderer.new({ H: 240, L: 65, C: 50 })
puts "✓ Explorer initialized at H=240° (Blue)"

cycle = explorer.generate_hexatonic_cycle
puts "\nHexatonic cycle discovered:"
cycle.each_with_index do |color, i|
  transform = if i == 0
                "Start"
              elsif i.odd?
                "L (Leading)"
              else
                "P (Parallel)"
              end
  hue_change = i > 0 ? "(+#{(color[:H] - cycle[i-1][:H]).round(0)}°)" : ""
  puts "  [#{i}] #{transform.ljust(15)} H=#{color[:H].round(0)}° #{hue_change}"
end

# =========================================================================
# Scenario 5: Harmonic Cadence Detection
# =========================================================================

puts "\n\nSCENARIO 5: Harmonic Cadence Detection"
puts "-" * 80
puts

cadence_builder = PLRColorRenderer.new({ H: 210, L: 65, C: 50 })
puts "✓ Started in Dominant zone (H=210°)"

# Build authentic cadence-like progression
cadence_builder.transform_relative(-1)
puts "Applied R inverse → Subdominant zone"

cadence_builder.transform_parallel(-1)
puts "Applied P inverse → Tonic zone"

analysis = cadence_builder.analyze_harmonic_progression
puts "\nCadence analysis:"
puts "  Progression: #{analysis[:progression_type]}"
puts "  Authentic cadence: #{analysis[:has_authentic_cadence]}"
puts "  Plagal cadence: #{analysis[:has_plagal_cadence]}"
puts "  Functions: #{analysis[:functions].join(' → ')}"

# =========================================================================
# Scenario 6: CRDT Command Integration
# =========================================================================

puts "\n\nSCENARIO 6: CRDT Command Integration"
puts "-" * 80
puts

crdt_agent = PLRColorRenderer.new({ H: 30, L: 65, C: 50 })
puts "✓ CRDT Agent initialized"

commands = [
  "plr P",
  "plr L",
  "plr R",
  "query color",
  "history"
]

puts "\nExecuting CRDT commands:"
commands.each do |cmd|
  begin
    result = crdt_agent.apply_crdt_command(cmd)
    if result.is_a?(Array)
      puts "  #{cmd} → #{result.length} colors in history"
    elsif result.is_a?(Hash)
      puts "  #{cmd} → current color H=#{result[:H].round(0)}°"
    else
      puts "  #{cmd} → executed"
    end
  rescue => e
    puts "  #{cmd} → error: #{e.message}"
  end
end

# =========================================================================
# Scenario 7: Full Workflow
# =========================================================================

puts "\n\nSCENARIO 7: Complete Workflow"
puts "-" * 80
puts

workflow = PLRColorRenderer.new({ H: 60, L: 65, C: 50 })
puts "✓ Workflow agent initialized at H=60°"

# Step 1: Explore
puts "\nStep 1: Exploration (generate color palette)"
4.times { workflow.transform_parallel(1) }
2.times { workflow.transform_leading_tone(1) }
puts "  → Generated #{workflow.color_history.length} colors"

# Step 2: Analyze
puts "\nStep 2: Harmonic Analysis"
workflow_analysis = workflow.analyze_harmonic_progression
puts "  → Progression type: #{workflow_analysis[:progression_type]}"
puts "  → Functional completeness: #{workflow_analysis[:closure][:function_count]}/3"

# Step 3: Learn
puts "\nStep 3: Preference Learning"
5.times do |i|
  idx1 = rand(0...workflow.color_history.length)
  idx2 = rand(0...workflow.color_history.length)
  next if idx1 == idx2
  workflow.record_preference(idx1, idx2)
end
puts "  → Recorded #{workflow.preferences.length} preferences"

# Step 4: Merge (simulated remote state)
puts "\nStep 4: CRDT Merge (distributed convergence)"
remote_state = {
  color_history: [
    { H: 15, L: 70, C: 45 },
    { H: 180, L: 60, C: 55 }
  ],
  preferences: [
    { preferred_color: { H: 15, L: 70, C: 45 }, rejected_color: { H: 180, L: 60, C: 55 }, gradient: 0.5 }
  ]
}
workflow.merge!(remote_state)
puts "  → Merged remote state: #{workflow.color_history.length} total colors"

# Step 5: Summary
puts "\nStep 5: Session Summary"
final_summary = workflow.session_summary
puts "  → Colors: #{final_summary[:colors_generated]}"
puts "  → Functions: #{final_summary[:harmonic_functions]}"
puts "  → Preferences: #{final_summary[:preferences_recorded]}"
puts "  → Progression: #{final_summary[:progression_type]}"

# =========================================================================
# Summary
# =========================================================================

puts "\n" + "=" * 80
puts "PHASE 5 INTEGRATION: ALL SCENARIOS COMPLETE"
puts "=" * 80
puts

puts "✓ Single-agent learning with PLR transformations"
puts "✓ Multi-agent convergence via CRDT merging"
puts "✓ Binary preference learning and gradient signals"
puts "✓ Hexatonic cycle discovery (P-L-P-L-P-L)"
puts "✓ Harmonic cadence detection"
puts "✓ CRDT command parsing and execution"
puts "✓ Complete end-to-end workflow"
puts

puts "Ready for:"
puts "  • Julia preference_learning_loop.jl integration"
puts "  • Real-time Sonic Pi synthesis"
puts "  • Distributed multi-agent color harmony"
puts "  • Production deployment with Fermyon"
puts
