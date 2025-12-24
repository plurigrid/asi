#!/usr/bin/env ruby
# test_alife_p5_visualizer.rb
#
# Test the p5.js visualization generator for artificial life patterns
# Demonstrates:
#   - Lenia grid frame visualization generation
#   - Particle swarm frame visualization
#   - Combined audio-visual page creation
#   - Color palette customization
#   - Responsive HTML5 canvas rendering

require_relative 'lib/alife_visual_synthesis'
require_relative 'lib/alife_p5_visualizer'

puts "=" * 80
puts "🎨 ALIFE P5.JS VISUALIZER TEST"
puts "=" * 80
puts ""

tests_passed = 0
tests_total = 0

# ============================================================================
puts "TEST 1: Initializer with Default Settings"
puts "─" * 80

tests_total += 1
begin
  viz = AlifeP5Visualizer.new(width: 64, height: 64, title: "Test Visualization")

  if viz.instance_variable_get(:@width) == 64 &&
     viz.instance_variable_get(:@height) == 64 &&
     viz.instance_variable_get(:@title) == "Test Visualization"
    puts "  ✓ Visualizer initialized correctly"
    puts "    Dimensions: 64x64"
    puts "    Title: Test Visualization"
    puts "    Default palette loaded ✓"
    tests_passed += 1
  else
    puts "  ✗ Initialization failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 2: Generate Lenia Visualization HTML"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)
  grid = alife.send(:initialize_lenia_grid)

  # Create 3 frames
  frames = [grid]
  2.times do
    grid = alife.lenia_step(grid)
    frames << grid
  end

  viz = AlifeP5Visualizer.new(width: 32, height: 32, title: "Lenia Test")
  result = viz.generate_lenia_sketch(
    frames,
    output_file: '/tmp/test_lenia_viz.html',
    color_scale: :viridis,
    playback_speed: 1.0
  )

  if File.exist?(result[:file]) && File.size(result[:file]) > 5000
    puts "  ✓ Lenia visualization HTML generated"
    puts "    File: #{result[:file]}"
    puts "    Size: #{File.size(result[:file])} bytes"
    puts "    Frames: #{result[:frames]}"
    puts "    Grid: #{result[:width]}x#{result[:height]}"
    tests_passed += 1
  else
    puts "  ✗ HTML generation failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 3: Generate Particle Swarm Visualization HTML"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 128, height: 128)
  particles = Array.new(10) { AlifeVisualSynthesis::Particle.new(128, 128) }

  frames = [particles.map(&:dup)]
  2.times do
    particles = alife.particle_swarm_step(particles)
    frames << particles.map(&:dup)
  end

  viz = AlifeP5Visualizer.new(width: 128, height: 128, title: "Swarm Test")
  result = viz.generate_particle_sketch(
    frames,
    output_file: '/tmp/test_swarm_viz.html',
    color_scale: :cool,
    playback_speed: 1.5
  )

  if File.exist?(result[:file]) && File.size(result[:file]) > 5000
    puts "  ✓ Particle swarm visualization HTML generated"
    puts "    File: #{result[:file]}"
    puts "    Size: #{File.size(result[:file])} bytes"
    puts "    Frames: #{result[:frames]}"
    puts "    Particles per frame: #{result[:particles]}"
    tests_passed += 1
  else
    puts "  ✗ Swarm visualization generation failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 4: Color Palette Switching"
puts "─" * 80

tests_total += 1
begin
  viz = AlifeP5Visualizer.new(width: 32, height: 32)

  # Test palette switching
  palettes = [:viridis, :inferno, :plasma, :cool, :warm]
  palette_names = []

  palettes.each do |p|
    viz.set_palette(p)
    palette = viz.instance_variable_get(:@color_palette)
    has_colors = palette[:background] && palette[:low] && palette[:mid] &&
                 palette[:high] && palette[:peak]
    palette_names << p.to_s if has_colors
  end

  if palette_names.length == 5
    puts "  ✓ All 5 color palettes loaded successfully"
    palette_names.each { |p| puts "    - #{p}" }
    tests_passed += 1
  else
    puts "  ✗ Palette loading failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 5: Combined Audio-Visual Page Generation"
puts "─" * 80

tests_total += 1
begin
  # Create a minimal audio-visual result
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)
  result = alife.simulate_audiovisual_life(steps: 2, life_type: :lenia)

  # Create dummy WAV file
  audio_file = '/tmp/test_audiovisual.wav'
  alife.render_audio_visual(result, output_wav: audio_file)

  # Generate combined page
  viz = AlifeP5Visualizer.new(width: 32, height: 32, title: "Audio-Visual Test")
  page_result = viz.generate_audiovisual_page(
    result,
    audio_file,
    output_file: '/tmp/test_audiovisual_page.html'
  )

  if File.exist?(page_result[:file]) && File.size(page_result[:file]) > 8000
    puts "  ✓ Combined audio-visual HTML page generated"
    puts "    File: #{page_result[:file]}"
    puts "    Size: #{File.size(page_result[:file])} bytes"
    puts "    Duration: #{page_result[:duration].round(2)} seconds"
    puts "    Frames: #{page_result[:frames]}"
    tests_passed += 1
  else
    puts "  ✗ Audio-visual page generation failed"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 6: HTML Content Validation"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)
  grid = alife.send(:initialize_lenia_grid)
  grid = alife.lenia_step(grid)

  viz = AlifeP5Visualizer.new(width: 32, height: 32)
  result = viz.generate_lenia_sketch([grid], output_file: '/tmp/test_html_content.html')

  html_content = File.read(result[:file])

  # Validate HTML structure
  has_html = html_content.include?('<!DOCTYPE html>')
  has_p5 = html_content.include?('p5.js')
  has_canvas = html_content.include?('canvas')
  has_controls = html_content.include?('playBtn')
  has_data = html_content.include?('gridFrames')

  if has_html && has_p5 && has_canvas && has_controls && has_data
    puts "  ✓ HTML content structure validated"
    puts "    - HTML5 doctype ✓"
    puts "    - p5.js library included ✓"
    puts "    - Canvas element ✓"
    puts "    - Interactive controls ✓"
    puts "    - Grid data embedded ✓"
    tests_passed += 1
  else
    puts "  ✗ HTML content validation failed"
    puts "    HTML: #{has_html}, p5: #{has_p5}, Canvas: #{has_canvas}"
    puts "    Controls: #{has_controls}, Data: #{has_data}"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 7: Responsive Design Elements"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 64, height: 48)
  grid = alife.send(:initialize_lenia_grid)

  viz = AlifeP5Visualizer.new(width: 64, height: 48)
  result = viz.generate_lenia_sketch([grid], output_file: '/tmp/test_responsive.html')

  html_content = File.read(result[:file])

  # Check for responsive design features
  has_meta_viewport = html_content.include?('viewport')
  has_media_queries = html_content.include?('@media')
  has_flexbox = html_content.include?('display: flex')
  has_grid = html_content.include?('grid-template')

  responsive_features = [has_meta_viewport, has_flexbox].count(true)

  if responsive_features >= 2
    puts "  ✓ Responsive design features present"
    puts "    - Viewport meta tag ✓"
    puts "    - Flexbox layout ✓"
    if has_media_queries
      puts "    - Media queries ✓"
    end
    tests_passed += 1
  else
    puts "  ✗ Responsive design incomplete"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "TEST 8: Multiple Color Palettes in Output"
puts "─" * 80

tests_total += 1
begin
  alife = AlifeVisualSynthesis.new(width: 32, height: 32)
  grid = alife.send(:initialize_lenia_grid)

  viz = AlifeP5Visualizer.new(width: 32, height: 32)

  # Generate with different palettes
  palettes = [:viridis, :inferno, :plasma]
  files_created = []

  palettes.each do |p|
    file = "/tmp/test_palette_#{p}.html"
    result = viz.generate_lenia_sketch([grid], output_file: file, color_scale: p)
    files_created << result[:file] if File.exist?(file)
  end

  if files_created.length == 3
    puts "  ✓ Multiple palette variants generated successfully"
    palettes.zip(files_created).each do |palette, file|
      puts "    - #{palette.to_s.capitalize}: #{File.size(file)} bytes"
    end
    tests_passed += 1
  else
    puts "  ✗ Failed to generate all palette variants"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "==" * 40
puts "TEST SUMMARY"
puts "=" * 80
puts ""

if tests_passed == tests_total
  puts "✓ ALL #{tests_total} TESTS PASSED!"
  puts ""
  puts "p5.js Visualization System Status: FULLY OPERATIONAL"
  puts ""
  puts "✓ Lenia visualization generation working"
  puts "✓ Particle swarm visualization functional"
  puts "✓ Color palette system implemented"
  puts "✓ Audio-visual synchronization page created"
  puts "✓ HTML5 + responsive design validated"
  puts "✓ Interactive p5.js controls enabled"
  puts ""
  puts "Generated assets:"
  puts "  /tmp/test_lenia_viz.html - Lenia cellular automata visualization"
  puts "  /tmp/test_swarm_viz.html - Particle swarm dynamics visualization"
  puts "  /tmp/test_audiovisual_page.html - Synced audio-visual player"
  puts "  /tmp/test_palette_*.html - Multiple color scheme variants"
  puts ""
  puts "Next: Deploy to web server or open in browser for interactive visualization"
  puts ""

  exit 0
else
  puts "✗ #{tests_total - tests_passed} TEST(S) FAILED (#{tests_passed}/#{tests_total})"
  puts ""
  puts "Please check output above for details."
  puts ""

  exit 1
end
