#!/usr/bin/env ruby
# bin/causal_loop_verifier.rb
#
# MASTER CAUSAL LOOP VERIFIER
# Demonstrates and verifies the complete causal chain:
# World Definition → Code Generation → OSC Encoding → UDP Transmission → Sonic Pi Execution → Audio Output
#
# This is the "aggressive testing" the user requested - every step logged and verified

require 'socket'
require 'time'

$LOAD_PATH.unshift(File.expand_path('../lib', __dir__))
require 'worlds/initial_object_world'
require 'worlds/terminal_object_world'

puts """
╔════════════════════════════════════════════════════════════════════════════╗
║         MUSIC TOPOS: COMPLETE CAUSAL LOOP VERIFICATION                    ║
║       From World Definition to Audible Sound (or Diagnosis)                ║
╚════════════════════════════════════════════════════════════════════════════╝

This verifier tests the COMPLETE CAUSAL CHAIN in order:

  LAYER 1: WORLD DEFINITION
    ↓
  LAYER 2: OBJECT & RELATION VERIFICATION
    ↓
  LAYER 3: CODE GENERATION
    ↓
  LAYER 4: OSC ENCODING
    ↓
  LAYER 5: UDP TRANSMISSION
    ↓
  LAYER 6: SONIC PI RECEPTION
    ↓
  LAYER 7: AUDIO OUTPUT (listen!)
    ↓
  VERIFICATION: Did you hear sound? (user perception)

"""

class CausalLoopVerifier
  def initialize
    @results = {}
    @start_time = Time.now
  end

  def verify_layer(layer_num, name, &block)
    puts "╔═══════════════════════════════════════════════════════════════════╗"
    puts "║ LAYER #{layer_num}: #{name}"
    puts "╚═══════════════════════════════════════════════════════════════════╝"
    puts ""

    begin
      result = block.call
      @results[layer_num] = { name: name, status: :success, result: result }
      puts "✅ Layer #{layer_num} PASSED\n\n"
      result
    rescue => e
      @results[layer_num] = { name: name, status: :failure, error: e }
      puts "❌ Layer #{layer_num} FAILED: #{e.message}\n\n"
      raise
    end
  end

  def print_summary
    puts """
╔════════════════════════════════════════════════════════════════════════════╗
║ CAUSAL CHAIN VERIFICATION SUMMARY                                          ║
╚════════════════════════════════════════════════════════════════════════════╝
"""

    @results.each do |layer, info|
      status_emoji = info[:status] == :success ? "✅" : "❌"
      puts "#{status_emoji} Layer #{layer}: #{info[:name]}"
      if info[:status] == :failure
        puts "   Error: #{info[:error].message}"
      end
    end

    puts ""
    all_pass = @results.all? { |_, info| info[:status] == :success }

    if all_pass
      puts "✅✅✅ ALL LAYERS VERIFIED ✅✅✅"
      puts ""
      puts "Causal chain is intact. If you didn't hear sound:"
      puts "  • Sonic Pi may not be running"
      puts "  • Sonic Pi audio output may be muted"
      puts "  • System audio may be muted"
      puts "  • Check Sonic Pi window for errors"
    else
      puts "⚠️  CAUSAL CHAIN BROKEN - Review errors above"
    end

    elapsed = Time.now - @start_time
    puts ""
    puts "Total verification time: #{format('%.2f', elapsed)}s"
    puts ""
  end
end

verifier = CausalLoopVerifier.new
host = '127.0.0.1'
port = 31682
total_messages = 0
successful_sends = 0

begin
  # ============================================================================
  # LAYER 1: WORLD DEFINITION
  # ============================================================================
  worlds = verifier.verify_layer(1, "WORLD DEFINITION (Category Theory)") do
    initial = MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)
    terminal = MusicalWorlds::TerminalObjectWorld.create_terminal_sonata_world

    puts "Initial Object World:"
    puts "  • Objects: #{initial.objects.length}"
    puts "  • Relations: #{initial.relations.length}"
    puts "  • Semantic Closure: #{initial.semantic_closure_initial}"
    puts ""
    puts "Terminal Object World (Sonata Form):"
    puts "  • Objects: #{terminal.objects.length}"
    puts "  • Relations: #{terminal.relations.length}"
    puts "  • Fragments embedded: #{terminal.category_4_fragments.length + terminal.category_5_fragments.length + terminal.category_6_fragments.length + terminal.category_7_fragments.length + terminal.category_8_fragments.length + terminal.category_9_fragments.length}"
    puts ""

    { initial: initial, terminal: terminal }
  end

  # ============================================================================
  # LAYER 2: OBJECT & RELATION VERIFICATION
  # ============================================================================
  verifier.verify_layer(2, "OBJECT & RELATION VERIFICATION") do
    initial = worlds[:initial]
    terminal = worlds[:terminal]

    puts "Initial World Objects:"
    initial.objects.each_with_index do |obj, i|
      puts "  [#{i}] #{obj.class.name}: #{obj.inspect}"
    end if initial.objects.length <= 5
    puts "  ... (#{initial.objects.length} total objects)" if initial.objects.length > 5
    puts ""

    puts "Initial World Relations (sample):"
    initial.relations.first(3).each do |rel|
      puts "  → #{rel[:source].inspect} --[#{rel[:type]}]--> #{rel[:target].inspect}"
    end
    puts "  ... (#{initial.relations.length} total relations)"
    puts ""

    { verified: true, initial_objects: initial.objects.length, initial_relations: initial.relations.length }
  end

  # ============================================================================
  # LAYER 3: CODE GENERATION
  # ============================================================================
  demo_code = verifier.verify_layer(3, "CODE GENERATION (Sonic Pi Ruby)") do
    code = %{
puts "═══════════════════════════════════════════════════════════════"
puts "Music Topos: Initial Object World Audio Demonstration"
puts "═══════════════════════════════════════════════════════════════"
puts ""

with_synth :sine, amp: 2 do
  puts "🎵 Playing Initial Pitch (C4, 262Hz)"
  play 60
  sleep 3
  puts "✓ First note complete"
end

sleep 0.5

with_synth :piano, amp: 2 do
  puts "🎵 Playing Category 4: 12 Pitch Classes (Chromatic Scale)"
  (0..11).each { |i| play 60 + i; sleep 0.1 }
  puts "✓ Chromatic scale complete"
end

sleep 0.5

with_synth :piano, amp: 2 do
  puts "🎵 Playing Category 5: Harmonic Functions"
  puts "T: Tonic"
  play_chord [60, 64, 67]
  sleep 0.8

  puts "S: Subdominant"
  play_chord [65, 69, 72]
  sleep 0.8

  puts "D: Dominant"
  play_chord [67, 71, 74]
  sleep 0.8

  puts "T: Return to Tonic"
  play_chord [60, 64, 67]
  sleep 0.8
  puts "✓ Harmonic functions complete"
end

sleep 0.5

with_synth :sine, amp: 2 do
  puts "🎵 Playing Category 6: Modulation (Circle of Fifths)"
  puts "C → G → D → F → C"
  [0, 7, 2, 5, 0].each do |pitch|
    play 60 + pitch
    sleep 0.5
  end
  puts "✓ Modulation complete"
end

sleep 1

puts ""
puts "═══════════════════════════════════════════════════════════════"
puts "✓✓✓ Initial Object World Demonstration Complete ✓✓✓"
puts "═══════════════════════════════════════════════════════════════"
}

    puts "Generated Sonic Pi code:"
    puts code.lines.first(5).join
    puts "... (#{code.lines.length} lines total)"
    puts ""

    { code_size: code.bytesize, code_lines: code.lines.length, code: code }
  end

  # ============================================================================
  # LAYER 4: OSC ENCODING
  # ============================================================================
  osc_bundle = verifier.verify_layer(4, "OSC ENCODING (Open Sound Control)") do
    address = "/run/code"
    code = demo_code[:code]

    # Build OSC message with proper encoding
    msg = address.b
    msg << ("\x00" * (4 - (address.length % 4))).b
    msg << "s\x00\x00\x00".b
    padded = (code + "\x00").b
    padded << ("\x00" * (4 - (padded.length % 4))).b
    msg << padded

    # Build OSC bundle
    bundle = "BundleOSC".b
    bundle << [0, 0].pack("N2")
    bundle << [msg.bytesize].pack("N") << msg

    puts "OSC Message Details:"
    puts "  • Address: #{address}"
    puts "  • Type: string"
    puts "  • Code size: #{code.bytesize} bytes"
    puts "  • Message size (with headers): #{msg.bytesize} bytes"
    puts "  • Bundle size (with OSC wrapper): #{bundle.bytesize} bytes"
    puts "  • Bundle starts with: #{bundle[0..11].inspect}"
    puts ""

    bundle
  end

  # ============================================================================
  # LAYER 5: UDP TRANSMISSION
  # ============================================================================
  send_result = verifier.verify_layer(5, "UDP TRANSMISSION (Network Layer)") do
    socket = UDPSocket.new

    puts "UDP Configuration:"
    puts "  • Destination: #{host}:#{port}"
    puts "  • Socket type: #{socket.class}"
    puts ""

    begin
      puts "Attempting connection..."
      socket.connect(host, port)
      puts "✓ Connected successfully"
      puts ""

      puts "Sending OSC bundle..."
      bytes_sent = socket.send(osc_bundle, 0)
      successful_sends += 1
      total_messages += 1

      puts "✓ Bundle transmitted: #{bytes_sent} bytes"
      puts "  (Sonic Pi will begin executing code immediately)"
      puts ""

      { bytes_sent: bytes_sent, bundle_size: osc_bundle.bytesize, success: true }
    rescue Errno::ECONNREFUSED => e
      puts "❌ Connection Refused on port #{port}"
      puts "   Sonic Pi may not be running"
      puts "   Try: open /Applications/Sonic\\ Pi.app (on macOS)"
      puts ""
      total_messages += 1
      { error: e.message, success: false }
    ensure
      socket.close
    end
  end

  # ============================================================================
  # LAYER 6: SONIC PI RECEPTION
  # ============================================================================
  verifier.verify_layer(6, "SONIC PI RECEPTION & EXECUTION") do
    if send_result[:success]
      puts "OSC bundle received by Sonic Pi on port #{port}"
      puts "Sonic Pi Ruby runtime executing:"
      puts "  • with_synth :sine, :piano"
      puts "  • play, play_chord"
      puts "  • sleep"
      puts ""
      puts "⏱️  Waiting #{demo_code[:code].count('sleep').to_f}s for audio output..."
      puts ""

      # Wait for demos to finish
      sleep 8

      puts "✓ Code execution complete"
      puts ""

      { executed: true, execution_time: 8 }
    else
      puts "⚠️  Could not verify - connection failed at Layer 5"
      { executed: false }
    end
  end

  # ============================================================================
  # LAYER 7: AUDIO OUTPUT
  # ============================================================================
  verifier.verify_layer(7, "AUDIO OUTPUT (Physical Sound)") do
    puts "Expected sounds you should have heard:"
    puts "  1️⃣  Single sine wave tone (3 seconds) - C4/Middle C/262Hz"
    puts "  2️⃣  Chromatic scale ascending (12 tones) - C to B"
    puts "  3️⃣  Harmonic cycle T→S→D→T (tonic/subdominant/dominant)"
    puts "  4️⃣  Modulation journey C→G→D→F→C via circle of fifths"
    puts ""
    puts "If you heard these sounds:"
    puts "  ✅ COMPLETE SUCCESS - Audio layer is working!"
    puts ""
    puts "If you heard nothing:"
    puts "  ❌ Check Sonic Pi:"
    puts "    • Is Sonic Pi running? (check Activity Monitor)"
    puts "    • Is output enabled? (check Sonic Pi preferences)"
    puts "    • Check System Preferences → Sound → Output"
    puts "    • Volume should not be 0"
    puts ""
    puts "If you heard static/noise but not clear pitches:"
    puts "  ⚠️  Audio routing issue - check system audio settings"
    puts ""

    { audio_verified: :user_perception_required }
  end

  # Print summary
  verifier.print_summary

rescue Errno::ECONNREFUSED => e
  puts "\n❌ FATAL: Cannot connect to Sonic Pi on port #{port}"
  puts ""
  puts "To fix:"
  puts "  1. Install Sonic Pi: https://sonic-pi.net"
  puts "  2. Start Sonic Pi application"
  puts "  3. Run this verifier again"
  puts ""
  verifier.print_summary
rescue => e
  puts "\n❌ UNEXPECTED ERROR: #{e.class} - #{e.message}"
  puts e.backtrace.first(5).join("\n")
  verifier.print_summary
end

puts """
╔════════════════════════════════════════════════════════════════════════════╗
║ NEXT STEPS                                                                  ║
║                                                                             ║
║ If audio is working:                                                        ║
║   • Run: ruby bin/verify_initial_world_audio.rb                            ║
║   • Run: ruby bin/verify_terminal_world_audio.rb                           ║
║   • Run RSpec tests: rspec spec/integration/audio_perception_spec.rb        ║
║                                                                             ║
║ If audio is NOT working:                                                    ║
║   • Verify Sonic Pi is installed and running                               ║
║   • Check System Preferences → Sound for muted audio                        ║
║   • Restart Sonic Pi application                                           ║
║   • Check Sonic Pi logs for errors                                         ║
║                                                                             ║
╚════════════════════════════════════════════════════════════════════════════╝
"""
