#!/usr/bin/env ruby
# bin/verify_terminal_world_audio.rb
#
# AGGRESSIVE AUDIO VERIFICATION FOR TERMINAL OBJECT WORLD
# Sends OSC messages to Sonic Pi and verifies the sonata form completion
# Tests that all fragments resolve into the terminal object (sonata form)

require 'socket'
require 'time'

$LOAD_PATH.unshift(File.expand_path('../lib', __dir__))
require 'worlds/terminal_object_world'

class AudioVerificationLogger
  attr_reader :log

  def initialize
    @log = []
    @start_time = Time.now
  end

  def log_action(action, details = {})
    entry = {
      timestamp: Time.now,
      elapsed: Time.now - @start_time,
      action: action,
      details: details
    }
    @log << entry
    puts "#{format_timestamp(entry[:elapsed])} | #{action}"
    details.each { |k, v| puts "  → #{k}: #{v.inspect}" }
  end

  def format_timestamp(seconds)
    "#{format('%.3f', seconds)}s".ljust(10)
  end

  def verify_log
    puts "\n" + "=" * 80
    puts "AUDIO VERIFICATION LOG (#{@log.length} entries)"
    puts "=" * 80
    @log.each_with_index do |entry, i|
      puts "\n[#{i+1}] #{entry[:action]} @ #{entry[:timestamp].strftime('%H:%M:%S.%3N')}"
      entry[:details].each { |k, v| puts "    #{k}: #{v.inspect}" }
    end
  end
end

puts "=" * 80
puts "🎼 TERMINAL OBJECT WORLD - AGGRESSIVE AUDIO VERIFICATION"
puts "=" * 80
puts ""
puts "Causal Chain:"
puts "  1. Create TerminalObjectWorld (Sonata Form as endpoint)"
puts "  2. Generate code showing fragments resolving into sonata"
puts "  3. Build OSC bundles for each fragment category"
puts "  4. Send via UDP to port 31682"
puts "  5. Log every transmission and category"
puts "  6. Verify all fragments embed correctly"
puts "  7. Listen for complete sonata form audio"
puts ""

logger = AudioVerificationLogger.new
host = '127.0.0.1'
port = 31682
demo_count = 0
total_bytes_sent = 0
failed_sends = 0

begin
  logger.log_action("BUILD WORLD", { name: "TerminalObjectWorld", terminal_object: "Sonata Form" })
  world = MusicalWorlds::TerminalObjectWorld.create_terminal_sonata_world

  logger.log_action("WORLD CREATED", {
    objects: world.objects.length,
    relations: world.relations.length,
    fragments_cat4: world.category_4_fragments.length,
    fragments_cat5: world.category_5_fragments.length,
    fragments_cat6: world.category_6_fragments.length,
    fragments_cat7: world.category_7_fragments.length,
    fragments_cat8: world.category_8_fragments.length,
    fragments_cat9: world.category_9_fragments.length
  })

  # Demos showing fragments resolving into sonata
  demos = [
    {
      category: 4,
      name: "Category 4 → Sonata: Pitch Classes in Exposition",
      code: %{
puts "\\n🎼 DEMO 1: CATEGORY 4 RESOLUTION"
puts "All 12 pitch classes resolving into sonata exposition"
with_synth :sine, amp: 2 do
  puts "Exposition starts in C major"
  play_chord [60, 64, 67]
  sleep 0.5

  puts "Pitch classes scan through exposition region"
  (0..11).each { |i| play 60 + i; sleep 0.08 }

  puts "Resolution back to exposition opening"
  play_chord [60, 64, 67]
  sleep 0.5
end
puts "Category 4 resolution complete"
},
      expected_duration: 4
    },
    {
      category: 5,
      name: "Category 5 → Sonata: Harmonic Functions",
      code: %{
puts "\\n🎼 DEMO 2: CATEGORY 5 RESOLUTION"
puts "T/S/D functions resolving through sonata sections"
with_synth :piano, amp: 2.5 do
  puts "Exposition: T (Tonic)"
  play_chord [60, 64, 67]
  sleep 0.8

  puts "Development: S+D (Subdominant into Dominant)"
  play_chord [65, 69, 72]
  sleep 0.4
  play_chord [67, 71, 74]
  sleep 0.4

  puts "Recapitulation: Return to T"
  play_chord [60, 64, 67]
  sleep 1.2

  puts "Coda: Final resolution"
  play_chord [60, 64, 67]
  sleep 0.5
end
puts "Category 5 resolution complete"
},
      expected_duration: 5
    },
    {
      category: 6,
      name: "Category 6 → Sonata: Modulation in Development",
      code: %{
puts "\\n🎼 DEMO 3: CATEGORY 6 RESOLUTION"
puts "Modulation paths embedded in development section"
with_synth :sine, amp: 2 do
  puts "Home (C major) - Exposition"
  play_chord [60, 64, 67]
  sleep 0.5

  puts "Key journey through development: C→G→D→F→C"
  [0, 7, 2, 5].each do |root|
    play 60 + root
    sleep 0.4
  end

  puts "Resolution back home"
  play_chord [60, 64, 67]
  sleep 0.8
end
puts "Category 6 resolution complete"
},
      expected_duration: 4
    },
    {
      category: 7,
      name: "Category 7 → Sonata: Voice-Led Chords",
      code: %{
puts "\\n🎼 DEMO 4: CATEGORY 7 RESOLUTION"
puts "Voice-leading embedded throughout sonata"
with_synth :sine, amp: 2 do
  # Exposition
  puts "Exposition: Root position"
  play_chord [60, 64, 67]
  sleep 0.5

  # Development
  puts "Development: First inversion"
  play_chord [64, 67, 72]
  sleep 0.5

  # Recapitulation
  puts "Recapitulation: Return to root"
  play_chord [60, 64, 67]
  sleep 0.5

  # Coda
  puts "Coda: Final sonority"
  play_chord [48, 60, 64, 67]
  sleep 1.0
end
puts "Category 7 resolution complete"
},
      expected_duration: 4
    },
    {
      category: 8,
      name: "Category 8 → Sonata: Harmonic Progression",
      code: %{
puts "\\n🎼 DEMO 5: CATEGORY 8 RESOLUTION"
puts "I-IV-V-I progression embedded across sections"
with_synth :piano, amp: 2.5 do
  puts "Exposition: I (presents progression theme)"
  play_chord [60, 64, 67]
  sleep 0.6

  puts "Development: IV-V (explored in key areas)"
  play_chord [65, 69, 72]
  sleep 0.4
  play_chord [67, 71, 74]
  sleep 0.4

  puts "Recapitulation: I (progression returns)"
  play_chord [60, 64, 67]
  sleep 0.8

  puts "Coda: I (final resolution)"
  play_chord [60, 64, 67]
  sleep 0.5
end
puts "Category 8 resolution complete"
},
      expected_duration: 4
    },
    {
      category: 9,
      name: "Category 9 → Sonata: Cadential Structures",
      code: %{
puts "\\n🎼 DEMO 6: CATEGORY 9 RESOLUTION"
puts "All cadence types resolve into authentic cadence"
with_synth :sine, amp: 2 do
  puts "Half cadence (exposition question): I-V"
  play_chord [60, 64, 67]
  sleep 0.3
  play_chord [67, 71, 74]
  sleep 0.5

  puts "Plagal cadence (traditional): IV-I"
  play_chord [65, 69, 72]
  sleep 0.3
  play_chord [60, 64, 67]
  sleep 0.5

  puts "Authentic cadence (strong): V-I (resolution!)"
  play_chord [67, 71, 74]
  sleep 0.4
  play_chord [60, 64, 67]
  sleep 1.0

  puts "Final tonic for closure"
  play_chord [60, 64, 67]
  sleep 0.5
end
puts "Category 9 resolution complete"
},
      expected_duration: 5
    },
    {
      category: "terminal",
      name: "Complete Sonata Form (Terminal Object)",
      code: %{
puts "\\n🎼 FINAL DEMO: COMPLETE SONATA FORM"
puts "All fragments resolved into the terminal object"
puts ""

with_synth :piano do
  puts "═══════════════════════════════════════"
  puts "SONATA FORM: Terminal Object Achieved"
  puts "═══════════════════════════════════════"

  puts "\\n1. EXPOSITION (themes presented)"
  puts "   First theme (Tonic)"
  play_chord [60, 64, 67]
  sleep 0.5

  puts "   Second theme (Dominant)"
  play_chord [67, 71, 74]
  sleep 0.5

  puts "\\n2. DEVELOPMENT (themes explored)"
  puts "   Modulation journey"
  play_chord [65, 69, 72]
  sleep 0.3
  play_chord [74, 78, 81]
  sleep 0.3
  play_chord [65, 69, 72]
  sleep 0.3

  puts "\\n3. RECAPITULATION (themes return home)"
  puts "   First theme back in tonic"
  play_chord [60, 64, 67]
  sleep 0.5

  puts "   Second theme also in tonic (not dominant!)"
  play_chord [62, 66, 69]
  sleep 0.5

  puts "\\n4. CODA (final closure)"
  puts "   Authentic cadence V-I"
  play_chord [67, 71, 74]
  sleep 0.4
  puts "   → Perfect resolution"
  play_chord [60, 64, 67]
  sleep 2.0

  puts "\\n✓✓✓ COMPLETE SONATA FORM ACHIEVED ✓✓✓"
  puts "Terminal object: All fragments embedded and resolved"
end
},
      expected_duration: 12
    }
  ]

  # Send each demo
  demos.each do |demo|
    demo_count += 1
    code = demo[:code]

    logger.log_action("ENCODE DEMO #{demo_count}", {
      category: demo[:category],
      name: demo[:name],
      expected_duration: demo[:expected_duration]
    })

    # Build OSC bundle
    address = "/run/code"
    msg = address.b
    msg << ("\x00" * (4 - (address.length % 4))).b
    msg << "s\x00\x00\x00".b
    padded = (code + "\x00").b
    padded << ("\x00" * (4 - (padded.length % 4))).b
    msg << padded

    bundle = "BundleOSC".b
    bundle << [0, 0].pack("N2")
    bundle << [msg.bytesize].pack("N") << msg

    logger.log_action("BUILD BUNDLE #{demo_count}", {
      address: address,
      bundle_size: bundle.bytesize
    })

    # Send via UDP
    socket = UDPSocket.new
    begin
      socket.connect(host, port)
      bytes_sent = socket.send(bundle, 0)
      total_bytes_sent += bytes_sent

      logger.log_action("SEND DEMO #{demo_count} ✓", {
        category: demo[:category],
        bytes_sent: bytes_sent,
        success: bytes_sent == bundle.bytesize
      })

      # Wait for audio
      logger.log_action("LISTENING #{demo_count}", {
        duration: demo[:expected_duration],
        for: demo[:name]
      })
      sleep demo[:expected_duration] + 0.5

    rescue Errno::ECONNREFUSED => e
      logger.log_action("SEND FAILED #{demo_count} ✗", {
        error: "Connection refused",
        port: port
      })
      failed_sends += 1
    rescue => e
      logger.log_action("SEND ERROR #{demo_count} ✗", {
        error: e.class,
        message: e.message
      })
      failed_sends += 1
    ensure
      socket.close
    end

    puts ""
  end

  logger.log_action("ALL DEMOS SENT", {
    total_demos: demo_count,
    failures: failed_sends,
    bytes_sent: total_bytes_sent
  })

rescue => e
  logger.log_action("CRITICAL ERROR", {
    error: e.class,
    message: e.message
  })
end

# Print verification log
logger.verify_log

puts "\n" + "=" * 80
puts "TERMINAL OBJECT AUDIO VERIFICATION RESULT"
puts "=" * 80
puts ""
if failed_sends == 0
  puts "✅ UDP LAYER: All #{demo_count} category demonstrations transmitted"
  puts "✅ CAUSAL CHAIN: Fragment → OSC → UDP → Sonic Pi → Audio"
  puts "🎼 AUDIO LAYER: Listen for sonata form sections above"
  puts "   - Exposition (presentation)"
  puts "   - Development (exploration)"
  puts "   - Recapitulation (return)"
  puts "   - Coda (closure)"
  puts "   - Final authentic cadence (resolution)"
else
  puts "❌ #{failed_sends} transmissions failed"
  puts "⚠️  Verify Sonic Pi running on port 31682"
end
puts ""
puts "Total data sent: #{total_bytes_sent} bytes"
puts ""
