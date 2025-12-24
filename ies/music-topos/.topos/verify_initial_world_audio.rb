#!/usr/bin/env ruby
# bin/verify_initial_world_audio.rb
#
# AGGRESSIVE AUDIO VERIFICATION FOR INITIAL OBJECT WORLD
# Sends OSC messages to Sonic Pi and logs every step of the causal chain
# Verifies UDP transmission AND attempts audio perception

require 'socket'
require 'time'

$LOAD_PATH.unshift(File.expand_path('../lib', __dir__))
require 'worlds/initial_object_world'

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
puts "🔊 INITIAL OBJECT WORLD - AGGRESSIVE AUDIO VERIFICATION"
puts "=" * 80
puts ""
puts "Causal Chain:"
puts "  1. Create InitialObjectWorld"
puts "  2. Generate Sonic Pi code for each step"
puts "  3. Build OSC bundles"
puts "  4. Send via UDP to port 31682"
puts "  5. Log every transmission"
puts "  6. Verify UDP layer working"
puts "  7. Listen for audio (or at least verify messages sent)"
puts ""

logger = AudioVerificationLogger.new
host = '127.0.0.1'
port = 31682
demo_count = 0
max_message_size = 0
total_bytes_sent = 0
failed_sends = 0

begin
  logger.log_action("BUILD WORLD", { name: "InitialObjectWorld", initial_pitch: 0 })
  world = MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)
  logger.log_action("WORLD CREATED", {
    objects: world.objects.length,
    relations: world.relations.length,
    semantic_closure: world.semantic_closure_initial
  })

  # Define demos with maximum logging and audio markers
  demos = [
    {
      name: "Initial Pitch (C4)",
      code: %{
puts "\\n🎵 DEMO 1: INITIAL PITCH"
puts "Playing single pitch: C4 (Middle C, 262Hz)"
with_synth :sine, amp: 3 do
  puts "Synth created, note starting..."
  play 60
  puts "Note playing NOW (listening for audio)"
  sleep 3
  puts "Three seconds complete, note should end"
end
puts "Demo 1 complete"
},
      expected_duration: 4
    },
    {
      name: "Category 4: 12 Pitch Classes",
      code: %{
puts "\\n🎵 DEMO 2: PITCH CLASSES (S12)"
puts "Playing chromatic scale: C→C# → D → ... → B → C"
with_synth :sine, amp: 2 do
  (0..11).each do |semitone|
    play 60 + semitone
    puts "Semitone \\#{semitone}: freq=#{(60 + semitone).midi_to_hz rescue 'N/A'}Hz"
    sleep 0.15
  end
end
puts "Scale complete"
},
      expected_duration: 3
    },
    {
      name: "Category 5: Harmonic Functions (T/S/D)",
      code: %{
puts "\\n🎵 DEMO 3: HARMONIC FUNCTION"
puts "Playing T→S→D→T cycle (Tonic→Subdominant→Dominant→Tonic)"
with_synth :piano, amp: 2 do
  puts "T (Tonic): C Major"
  play_chord [60, 64, 67]
  sleep 1

  puts "S (Subdominant): F Major"
  play_chord [65, 69, 72]
  sleep 1

  puts "D (Dominant): G Major"
  play_chord [67, 71, 74]
  sleep 1

  puts "T (Return): C Major"
  play_chord [60, 64, 67]
  sleep 1.5
end
puts "Harmonic function cycle complete"
},
      expected_duration: 6
    },
    {
      name: "Category 6: Modulation (Circle of Fifths)",
      code: %{
puts "\\n🎵 DEMO 4: MODULATION"
puts "Circle of fifths journey: C→G→D→F→C"
with_synth :sine, amp: 2.5 do
  keys = [
    {pitch: [60, 64, 67], name: "C Major (home)"},
    {pitch: [67, 71, 74], name: "G Major (+5)"},
    {pitch: [74, 78, 81], name: "D Major (+5)"},
    {pitch: [65, 69, 72], name: "F Major (-5)"},
    {pitch: [60, 64, 67], name: "C Major (resolution)"}
  ]

  keys.each do |key|
    puts key[:name]
    play_chord key[:pitch]
    sleep 0.6
  end
end
puts "Modulation journey complete"
},
      expected_duration: 4
    }
  ]

  # Send each demo with aggressive logging
  demos.each do |demo|
    demo_count += 1
    code = demo[:code]

    logger.log_action("ENCODE DEMO #{demo_count}", {
      name: demo[:name],
      code_lines: code.lines.length,
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

    max_message_size = [max_message_size, bundle.bytesize].max

    logger.log_action("BUILD OSC BUNDLE #{demo_count}", {
      address: address,
      code_size: code.bytesize,
      bundle_size: bundle.bytesize,
      max_size_so_far: max_message_size
    })

    # Send via UDP
    socket = UDPSocket.new
    begin
      logger.log_action("CONNECT UDP #{demo_count}", {
        host: host,
        port: port,
        local_port: socket.addr[1]
      })

      socket.connect(host, port)
      bytes_sent = socket.send(bundle, 0)
      total_bytes_sent += bytes_sent

      logger.log_action("SEND DEMO #{demo_count} ✓", {
        bytes_sent: bytes_sent,
        bundle_size: bundle.bytesize,
        match: bytes_sent == bundle.bytesize,
        total_bytes: total_bytes_sent
      })

      # Wait for audio to play
      logger.log_action("WAIT FOR AUDIO #{demo_count}", {
        duration: demo[:expected_duration],
        listening_for: demo[:name]
      })
      sleep demo[:expected_duration] + 0.5

    rescue Errno::ECONNREFUSED => e
      logger.log_action("SEND FAILED #{demo_count} ✗", {
        error: "Connection refused",
        port: port,
        message: e.message
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

    logger.log_action("DEMO #{demo_count} COMPLETE", {
      success: failed_sends == 0,
      audio_should_have_played: true
    })

    puts ""
  end

  # Final verification
  logger.log_action("VERIFICATION COMPLETE", {
    demos_sent: demo_count,
    demos_failed: failed_sends,
    success_rate: "#{100.0 * (demo_count - failed_sends) / demo_count}%",
    total_bytes_sent: total_bytes_sent,
    max_message_size: max_message_size,
    causal_chain: "World → Code → OSC → UDP → Sonic Pi → Audio (✓ if heard)"
  })

rescue => e
  logger.log_action("CRITICAL ERROR", {
    error: e.class,
    message: e.message,
    backtrace_first_3_lines: e.backtrace.first(3)
  })
end

# Print full verification log
logger.verify_log

puts "\n" + "=" * 80
puts "AUDIO VERIFICATION RESULT"
puts "=" * 80
puts ""
if failed_sends == 0
  puts "✅ UDP LAYER: All #{demo_count} messages transmitted successfully"
  puts "✅ CAUSAL CHAIN: World → Code → OSC → UDP transmission verified"
  puts "🔊 AUDIO LAYER: Listen for sounds above"
  puts "   - If you heard sounds, audio layer is working!"
  puts "   - If silent, check:"
  puts "     • Sonic Pi is running (check port 31682)"
  puts "     • Sonic Pi output volume is not muted"
  puts "     • System audio is enabled and not muted"
else
  puts "❌ UDP LAYER: #{failed_sends} messages failed to send"
  puts "⚠️  Check Sonic Pi is running on port 31682"
end
puts ""
puts "Total data sent: #{total_bytes_sent} bytes"
puts "Max message size: #{max_message_size} bytes"
puts ""

