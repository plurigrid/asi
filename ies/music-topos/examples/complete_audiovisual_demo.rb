#!/usr/bin/env ruby
#
# Complete Audio-Visual Life Synthesis Demonstration
#
# End-to-end example showing:
# 1. Artificial life pattern generation (Lenia + particle swarms)
# 2. Audio synthesis from visual patterns
# 3. Professional audio effects processing
# 4. p5.js visualization rendering
# 5. Combined audio-visual output
#
# This demonstrates the full music-topos audio-visual art toolkit
# integrating artificial life, synthesis, effects, and visualization.
#

require_relative '../lib/alife_visual_synthesis'
require_relative '../lib/alife_p5_visualizer'
require_relative '../lib/audio_synthesis'
require_relative '../lib/audio_effects'

puts ""
puts "=" * 80
puts "🎨 COMPLETE AUDIO-VISUAL LIFE SYNTHESIS DEMONSTRATION"
puts "=" * 80
puts ""

# ===========================================================================
# CONFIGURATION
# ===========================================================================

puts "CONFIGURATION"
puts "-" * 80

OUTPUT_DIR = './output_audiovisual'
Dir.mkdir(OUTPUT_DIR) unless Dir.exist?(OUTPUT_DIR)

# Simulation parameters
GRID_WIDTH = 64
GRID_HEIGHT = 64
SIMULATION_STEPS = 10
PARTICLE_COUNT = 25

puts "Output directory: #{OUTPUT_DIR}"
puts "Grid dimensions: #{GRID_WIDTH}x#{GRID_HEIGHT}"
puts "Simulation steps: #{SIMULATION_STEPS}"
puts "Particle count: #{PARTICLE_COUNT}"
puts ""

# ===========================================================================
# PHASE 1: LENIA CELLULAR AUTOMATA + AUDIO SYNTHESIS
# ===========================================================================

puts "PHASE 1: Lenia Cellular Automata Synthesis"
puts "-" * 80

puts "Creating Lenia simulation..."
alife = AlifeVisualSynthesis.new(width: GRID_WIDTH, height: GRID_HEIGHT)

# Simulate Lenia with audio synthesis
puts "Running #{SIMULATION_STEPS} simulation steps..."
lenia_result = alife.simulate_audiovisual_life(
  steps: SIMULATION_STEPS,
  life_type: :lenia
)

puts "✓ Lenia simulation complete"
puts "  Frames generated: #{lenia_result[:visual_frames].length}"
puts "  Audio samples: #{lenia_result[:audio_samples].length}"
puts "  Duration: #{lenia_result[:duration_seconds].round(2)} seconds"
puts ""

# ===========================================================================
# PHASE 2: PARTICLE SWARM SIMULATION
# ===========================================================================

puts "PHASE 2: Particle Swarm Dynamics"
puts "-" * 80

puts "Creating particle swarm simulation..."
swarm_result = alife.simulate_audiovisual_life(
  steps: SIMULATION_STEPS,
  life_type: :swarm
)

puts "✓ Particle swarm simulation complete"
puts "  Frames generated: #{swarm_result[:visual_frames].length}"
puts "  Audio samples: #{swarm_result[:audio_samples].length}"
puts "  Duration: #{swarm_result[:duration_seconds].round(2)} seconds"
puts ""

# ===========================================================================
# PHASE 3: AUDIO EFFECTS PROCESSING
# ===========================================================================

puts "PHASE 3: Professional Audio Effects"
puts "-" * 80

puts "Creating effect chains..."

# Create sophisticated effect chains
lenia_effects = [
  { effect: :reverb, params: { room_size: 0.7, damping: 0.5, wet_mix: 0.35 } },
  { effect: :delay, params: { delay_time: 0.375, feedback: 0.3, wet_mix: 0.25 } },
  { effect: :chorus, params: { delay_time: 0.015, rate: 1.2, depth: 0.0015 } }
]

swarm_effects = [
  { effect: :delay, params: { delay_time: 0.5, feedback: 0.35, wet_mix: 0.3 } },
  { effect: :reverb, params: { room_size: 0.5, damping: 0.6, wet_mix: 0.3 } },
  { effect: :tremolo, params: { rate: 3.5, depth: 0.4 } }
]

puts "Applying effects to Lenia audio..."
audio_effects = AudioEffects.new
lenia_processed = audio_effects.apply_effects(lenia_result[:audio_samples], lenia_effects)

puts "Applying effects to swarm audio..."
swarm_processed = audio_effects.apply_effects(swarm_result[:audio_samples], swarm_effects)

puts "✓ Audio effects processing complete"
puts "  Lenia effect chain: Reverb → Delay → Chorus"
puts "  Swarm effect chain: Delay → Reverb → Tremolo"
puts ""

# ===========================================================================
# PHASE 4: p5.js VISUALIZATION GENERATION
# ===========================================================================

puts "PHASE 4: p5.js Visualization Rendering"
puts "-" * 80

puts "Creating visualization system..."
viz = AlifeP5Visualizer.new(width: GRID_WIDTH, height: GRID_HEIGHT)

# Generate Lenia visualization
puts "Generating Lenia interactive visualization..."
lenia_viz = viz.generate_lenia_sketch(
  lenia_result[:visual_frames],
  output_file: "#{OUTPUT_DIR}/lenia_interactive.html",
  color_scale: :viridis,
  playback_speed: 1.0
)

puts "✓ Lenia visualization: #{lenia_viz[:file]}"
puts "  Size: #{File.size(lenia_viz[:file])} bytes"
puts ""

# Generate particle swarm visualization
puts "Generating particle swarm interactive visualization..."
viz.set_palette(:cool)  # Different palette for swarms
swarm_viz = viz.generate_particle_sketch(
  swarm_result[:visual_frames],
  output_file: "#{OUTPUT_DIR}/swarm_interactive.html",
  color_scale: :cool,
  playback_speed: 1.2
)

puts "✓ Swarm visualization: #{swarm_viz[:file]}"
puts "  Size: #{File.size(swarm_viz[:file])} bytes"
puts ""

# ===========================================================================
# PHASE 5: WAV FILE GENERATION
# ===========================================================================

puts "PHASE 5: WAV Audio File Generation"
puts "-" * 80

audio_synth = AudioSynthesis.new

puts "Rendering Lenia audio to WAV..."
lenia_wav = "#{OUTPUT_DIR}/lenia_synthesis.wav"
audio_synth.write_wav_file(lenia_processed, lenia_wav)

puts "Rendering swarm audio to WAV..."
swarm_wav = "#{OUTPUT_DIR}/swarm_synthesis.wav"
audio_synth.write_wav_file(swarm_processed, swarm_wav)

puts "✓ WAV files generated"
puts "  Lenia: #{lenia_wav} (#{File.size(lenia_wav)} bytes)"
puts "  Swarm: #{swarm_wav} (#{File.size(swarm_wav)} bytes)"
puts ""

# ===========================================================================
# PHASE 6: COMBINED AUDIO-VISUAL PAGES
# ===========================================================================

puts "PHASE 6: Combined Audio-Visual Pages"
puts "-" * 80

# Copy WAV files to output directory for easy access
puts "Creating combined audio-visual pages..."

# For Lenia
lenia_result_copy = lenia_result.dup
lenia_result_copy[:audio_samples] = lenia_processed

lenia_page = viz.generate_audiovisual_page(
  lenia_result_copy,
  lenia_wav,
  output_file: "#{OUTPUT_DIR}/lenia_audiovisual.html"
)

puts "✓ Lenia audio-visual page: #{lenia_page[:file]}"

# For Swarms
swarm_result_copy = swarm_result.dup
swarm_result_copy[:audio_samples] = swarm_processed

viz.set_palette(:warm)
swarm_page = viz.generate_audiovisual_page(
  swarm_result_copy,
  swarm_wav,
  output_file: "#{OUTPUT_DIR}/swarm_audiovisual.html"
)

puts "✓ Swarm audio-visual page: #{swarm_page[:file]}"
puts ""

# ===========================================================================
# PHASE 7: SUMMARY & NEXT STEPS
# ===========================================================================

puts "=" * 80
puts "GENERATION COMPLETE"
puts "=" * 80
puts ""

puts "📊 SUMMARY STATISTICS"
puts "-" * 80
puts "Lenia:"
puts "  Visual frames: #{lenia_result[:visual_frames].length}"
puts "  Audio duration: #{lenia_result[:duration_seconds].round(2)}s"
puts "  Effects applied: 3 (Reverb, Delay, Chorus)"
puts ""
puts "Particle Swarms:"
puts "  Visual frames: #{swarm_result[:visual_frames].length}"
puts "  Audio duration: #{swarm_result[:duration_seconds].round(2)}s"
puts "  Particles: #{PARTICLE_COUNT}"
puts "  Effects applied: 3 (Delay, Reverb, Tremolo)"
puts ""

puts "📁 OUTPUT FILES"
puts "-" * 80
Dir.glob("#{OUTPUT_DIR}/*").each do |file|
  size_kb = (File.size(file) / 1024.0).round(1)
  puts "  #{File.basename(file)}: #{size_kb} KB"
end
puts ""

puts "🎯 HOW TO USE"
puts "-" * 80
puts "1. Open HTML files in a modern web browser:"
puts "   - lenia_interactive.html - Watch Lenia evolution in real-time"
puts "   - swarm_interactive.html - Observe Boid swarm dynamics"
puts "   - lenia_audiovisual.html - Synced audio + visual player"
puts "   - swarm_audiovisual.html - Synced audio + visual player"
puts ""
puts "2. Play audio files with any player:"
puts "   - lenia_synthesis.wav - Lenia-generated audio with effects"
puts "   - swarm_synthesis.wav - Swarm-generated audio with effects"
puts ""

puts "🎨 FEATURES DEMONSTRATED"
puts "-" * 80
puts "✓ Artificial life systems (Lenia, Boid particle swarms)"
puts "✓ Audio synthesis from visual patterns"
puts "✓ Professional audio effects (reverb, delay, chorus, tremolo)"
puts "✓ Real-time interactive p5.js visualizations"
puts "✓ Multiple color palettes (viridis, cool, warm, etc.)"
puts "✓ Responsive HTML5 design"
puts "✓ WAV file generation with high-quality audio"
puts "✓ Complete audio-visual integration"
puts ""

puts "🔗 INTEGRATION POINTS"
puts "-" * 80
puts "This demonstration integrates:"
puts "  • AlifeVisualSynthesis: Lenia + particle swarm simulation"
puts "  • AudioSynthesis: WAV generation from frequencies"
puts "  • AudioEffects: Professional effect processing"
puts "  • AlifeP5Visualizer: Interactive p5.js rendering"
puts "  • Gray Area Curriculum: Creative coding education toolkit"
puts "  • Laura Porta's Work: Visualization + movement tracking"
puts ""

puts "🚀 NEXT STEPS"
puts "-" * 80
puts "1. Deploy HTML files to web server for sharing"
puts "2. Create interactive parameter UI for real-time exploration"
puts "3. Integrate with Live Code education framework"
puts "4. Add MIDI/OSC control for live performance"
puts "5. Extend to GPU-accelerated rendering (WebGL)"
puts "6. Create preset library of interesting life forms (Orbium, Spot, etc.)"
puts ""

puts "✅ Session Complete!"
puts "=" * 80
puts ""
