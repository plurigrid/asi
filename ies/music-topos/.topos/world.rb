#!/usr/bin/env ruby
# bin/world.rb
#
# MUSIC TOPOS: CORE WORLD RUNNER
# Essential integration of world definitions with Sonic Pi audio
# Uses live_loop and direct note scheduling for reliability

require 'socket'

$LOAD_PATH.unshift(File.expand_path('../lib', __dir__))
require 'worlds/initial_object_world'
require 'worlds/terminal_object_world'

class WorldRunner
  def initialize(world_name = :initial)
    @world_name = world_name
    @host = '127.0.0.1'
    @port = 31682
  end

  def run
    puts "🎵 Music Topos: #{@world_name.to_s.capitalize} Object World"
    puts "─" * 60
    puts ""

    # Create world
    world = case @world_name
            when :initial
              MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)
            when :terminal
              MusicalWorlds::TerminalObjectWorld.create_terminal_sonata_world
            end

    # Report world state
    puts "World created: #{world.objects.length} objects, #{world.relations.length} relations"
    puts ""

    # Generate and send audio code
    send_world_audio(world)
  end

  private

  def send_world_audio(world)
    case @world_name
    when :initial
      play_initial_world(world)
    when :terminal
      play_terminal_world(world)
    end
  end

  def play_initial_world(world)
    pitches = (0..11).map { |i| 60 + i }

    code = %{
use_bpm 120

puts "═" * 40
puts "Initial Object World"
puts "═" * 40

use_synth :sine

puts "1. Initial Pitch (C4)"
play 60, sustain: 2
sleep 3

puts "2. Pitch Classes (all 12)"
#{pitches.map { |p| "play #{p}, sustain: 0.08; sleep 0.1" }.join("\n")}

puts "3. Harmonic Functions (T-S-D)"
use_synth :piano
play_chord [60, 64, 67], sustain: 0.8
sleep 1
play_chord [65, 69, 72], sustain: 0.8
sleep 1
play_chord [67, 71, 74], sustain: 0.8
sleep 1
play_chord [60, 64, 67], sustain: 0.8
sleep 1

puts "4. Modulation (Circle of Fifths)"
use_synth :sine
[0, 7, 2, 5, 0].each { |p| play 60 + p, sustain: 0.5; sleep 0.6 }

puts "✓ Complete"
}

    send_code(code)
  end

  def play_terminal_world(world)
    code = %{
use_bpm 120

puts "═" * 40
puts "Terminal Object World (Sonata Form)"
puts "═" * 40

puts "EXPOSITION: Presentation of themes"
use_synth :piano
play_chord [60, 64, 67], sustain: 0.8
sleep 1
play_chord [67, 71, 74], sustain: 0.8
sleep 1

puts "DEVELOPMENT: Exploration of key areas"
use_synth :sine
[65, 69, 72].each { |c| play c, sustain: 0.4; sleep 0.5 }
[74, 78, 81].each { |c| play c, sustain: 0.4; sleep 0.5 }

puts "RECAPITULATION: Return to home"
use_synth :piano
play_chord [60, 64, 67], sustain: 0.8
sleep 1

puts "CODA: Final closure with authentic cadence"
play_chord [67, 71, 74], sustain: 0.4
sleep 0.5
play_chord [60, 64, 67], sustain: 2
sleep 2

puts "✓ Sonata form complete"
}

    send_code(code)
  end

  def send_code(code)
    socket = UDPSocket.new

    begin
      socket.connect(@host, @port)

      # Build OSC message
      address = "/run/code"
      msg = address.b
      msg << ("\x00" * (4 - (address.length % 4))).b
      msg << "s\x00\x00\x00".b
      padded = (code + "\x00").b
      padded << ("\x00" * (4 - (padded.length % 4))).b
      msg << padded

      # Build bundle
      bundle = "BundleOSC".b
      bundle << [0, 0].pack("N2")
      bundle << [msg.bytesize].pack("N") << msg

      # Send
      bytes = socket.send(bundle, 0)
      puts "✓ Code sent to Sonic Pi (#{bytes} bytes)"
      puts "  Playing audio (listen now)..."
      puts ""

      # Wait for audio to finish
      case @world_name
      when :initial
        sleep 12  # ~10s of audio + buffer
      when :terminal
        sleep 14  # ~12s of audio + buffer
      end

      puts ""
      puts "✓ Audio playback complete"

    rescue Errno::ECONNREFUSED
      puts "✗ Cannot connect to Sonic Pi on port #{@port}"
      puts "  Make sure Sonic Pi is running"
      exit 1
    ensure
      socket.close
    end
  end
end

# Run specified world
world_type = ARGV[0]&.to_sym || :initial
valid_worlds = [:initial, :terminal]

unless valid_worlds.include?(world_type)
  puts "Usage: #{$0} [initial|terminal]"
  puts ""
  puts "Examples:"
  puts "  #{$0} initial    # Run initial object world (emergence)"
  puts "  #{$0} terminal   # Run terminal object world (resolution)"
  exit 1
end

runner = WorldRunner.new(world_type)
runner.run
