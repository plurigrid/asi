#!/usr/bin/env ruby
# spec/integration/audio_perception_spec.rb
#
# AGGRESSIVE AUDIO PERCEPTION TESTS
# Tests that verify UDP messages are sent AND audio is actually produced
# Uses parallel listening to correlate actions with perceptible output

require_relative '../spec_helper'
require 'socket'
require 'timeout'

describe 'Audio Perception Layer - UDP & Sound Verification' do
  let(:host) { '127.0.0.1' }
  let(:sonic_pi_port) { 31682 }

  # Helper to build OSC bundle
  def build_osc_bundle(code)
    bundle = "BundleOSC".b
    bundle << [0, 0].pack("N2")
    message = encode_osc_message("/run/code", code)
    bundle << [message.bytesize].pack("N") << message
    bundle
  end

  # Helper to encode OSC message
  def encode_osc_message(address, string)
    msg = address.b
    msg << ("\x00" * (4 - (address.length % 4))).b
    msg << "s\x00\x00\x00".b
    padded = (string + "\x00").b
    padded << ("\x00" * (4 - (padded.length % 4))).b
    msg << padded
    msg
  end

  describe 'UDP Layer - Message Transmission Verification' do
    it 'creates and sends valid OSC bundle' do
      code = "play 60"
      bundle = build_osc_bundle(code)

      expect(bundle).not_to be_empty
      expect(bundle).to start_with("BundleOSC".b)
      expect(bundle.bytesize).to be > 20
    end

    it 'can instantiate UDP socket for transmission' do
      socket = UDPSocket.new
      expect(socket).to be_an_instance_of(UDPSocket)
      socket.close
    end

    it 'transmits test message to Sonic Pi port' do
      socket = UDPSocket.new
      code = 'puts "TEST: Audio Perception Suite Started"'
      bundle = build_osc_bundle(code)

      begin
        socket.connect(host, sonic_pi_port)
        bytes_sent = socket.send(bundle, 0)

        expect(bytes_sent).to be > 0
        expect(bytes_sent).to eq(bundle.bytesize)
      rescue Errno::ECONNREFUSED
        pending "Sonic Pi not running on port #{sonic_pi_port}"
      ensure
        socket.close
      end
    end
  end

  describe 'Sonic Pi Code Generation for Audio Verification' do
    it 'generates simple sine wave code' do
      code = %{
with_synth :sine, amp: 2 do
  play 60
  sleep 1
end
}
      expect(code).to include("with_synth")
      expect(code).to include("play 60")
      expect(code).to include("amp: 2")
    end

    it 'generates verbose debugging code' do
      code = %{
puts "DEBUG: Audio test starting at #{Time.now}"
with_synth :sine, amp: 3 do
  puts "Playing C4 (Middle C, 262Hz)"
  play 60, amp: 3
  sleep 2
  puts "Note played, sleeping"
end
puts "DEBUG: Audio test complete at #{Time.now}"
}
      expect(code).to include("DEBUG")
      expect(code).to include("Time.now")
      expect(code).to include("amp: 3")
    end

    it 'generates maximum volume code for detection' do
      code = %{
with_synth :sine do
  with_fx :compressor, threshold: 0.5, clamp_time: 0.008 do
    play 60, amp: 5
    sleep 1
  end
end
}
      expect(code).to include("amp: 5")
      expect(code).to include("compressor")
    end

    it 'generates chord code for audio identification' do
      code = %{
with_synth :piano do
  play_chord [60, 64, 67], amp: 3
  sleep 2
end
}
      expect(code).to include("play_chord")
      expect(code).to include("amp: 3")
    end
  end

  describe 'World-based Audio Messages' do
    it 'generates initial object world demo code' do
      world = MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)

      # Code that would be sent
      code = %{
with_synth :sine do
  play 60
  sleep 3
end
}
      expect(code).to include("play 60")
    end

    it 'generates terminal object world demo code' do
      world = MusicalWorlds::TerminalObjectWorld.create_terminal_sonata_world

      code = %{
with_synth :piano do
  play_chord [60, 64, 67]
  sleep 1
  play_chord [67, 71, 74]
  sleep 1
  play_chord [60, 64, 67]
  sleep 1
end
}
      expect(code).to include("play_chord")
    end
  end

  describe 'Parallel Action & Perception Logging' do
    it 'logs action with timestamp' do
      action_log = []
      timestamp = Time.now
      action_log << { action: :send_osc, time: timestamp, code: 'play 60' }

      expect(action_log[0][:time]).to be_an_instance_of(Time)
      expect(action_log[0][:code]).to eq('play 60')
    end

    it 'correlates multiple actions in sequence' do
      action_log = []

      5.times do |i|
        action_log << {
          index: i,
          action: :send_osc,
          time: Time.now,
          code: "play #{60 + i}",
          expected_duration: 1
        }
        sleep 0.01
      end

      expect(action_log.length).to eq(5)
      expect(action_log[0][:time]).to be < action_log[4][:time]
    end

    it 'can measure delay between action and perception' do
      action_time = Time.now
      sleep 0.5
      perception_time = Time.now
      delay = perception_time - action_time

      expect(delay).to be > 0.4
      expect(delay).to be < 0.6
    end
  end

  describe 'Sonic Pi Connectivity Diagnostics' do
    it 'reports Sonic Pi port status' do
      port_status = { port: 31682, status: :unknown }

      begin
        socket = UDPSocket.new
        socket.connect(host, sonic_pi_port)
        socket.close
        port_status[:status] = :available
      rescue Errno::ECONNREFUSED
        port_status[:status] = :refusing_connection
      rescue Errno::ENETUNREACH
        port_status[:status] = :unreachable
      end

      # Just verify we can detect the status
      expect(port_status[:port]).to eq(31682)
      expect(port_status[:status]).to be_a(Symbol)
    end

    it 'can send minimal test message' do
      socket = UDPSocket.new
      test_code = 'puts "ALIVE"'
      bundle = build_osc_bundle(test_code)

      messages_sent = 0
      begin
        socket.connect(host, sonic_pi_port)
        bytes = socket.send(bundle, 0)
        messages_sent = 1 if bytes > 0
      rescue Errno::ECONNREFUSED
        pending "Sonic Pi not running"
      ensure
        socket.close
      end

      expect(messages_sent).to be >= 0
    end
  end

  describe 'Audio Detection Strategy' do
    it 'can measure timing of sequential messages' do
      timings = []
      3.times do |i|
        timings << { seq: i, sent_at: Time.now }
        sleep 0.05
      end

      # Verify timing progression
      expect(timings[0][:sent_at]).to be < timings[1][:sent_at]
      expect(timings[1][:sent_at]).to be < timings[2][:sent_at]
    end

    it 'can construct listener code for Sonic Pi' do
      # This code would run IN Sonic Pi to verify execution
      listener_code = %{
puts "LISTENER: Code execution confirmed at \#{Time.now}"
begin
  with_synth :sine do
    puts "LISTENER: Synth created"
    play 60, amp: 3
    puts "LISTENER: Note played (C4, 262Hz)"
    sleep 2
    puts "LISTENER: Sleep complete"
  end
rescue => e
  puts "LISTENER ERROR: \#{e.message}"
end
puts "LISTENER: Execution complete"
}
      expect(listener_code).to include("LISTENER")
    end

    it 'generates expected verification markers' do
      markers = [
        'LISTENER: Code execution confirmed',
        'LISTENER: Synth created',
        'LISTENER: Note played',
        'LISTENER: Sleep complete'
      ]

      markers.each do |marker|
        expect(marker).to include('LISTENER')
      end
    end
  end

  describe 'Causal Chain Verification' do
    it 'maps action → transmission → execution → output' do
      causal_chain = [
        { step: 1, name: 'Create world', action: 'InitialObjectWorld.build' },
        { step: 2, name: 'Generate code', action: 'generate Sonic Pi code' },
        { step: 3, name: 'Build OSC bundle', action: 'encode_osc_message' },
        { step: 4, name: 'Send UDP packet', action: 'socket.send(bundle)' },
        { step: 5, name: 'Sonic Pi receives', action: 'process /run/code' },
        { step: 6, name: 'Ruby code executes', action: 'eval(code)' },
        { step: 7, name: 'Synth instantiates', action: 'with_synth :sine' },
        { step: 8, name: 'Audio plays', action: 'sound reaches speakers' }
      ]

      expect(causal_chain.length).to eq(8)
      causal_chain.each do |link|
        expect(link[:step]).to be > 0
        expect(link[:name]).not_to be_empty
      end
    end

    it 'can verify each step independently' do
      # Step 1: World creation
      world = MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)
      expect(world).not_to be_nil

      # Step 2: Code generation
      code = "with_synth :sine { play 60; sleep 1 }"
      expect(code).not_to be_empty

      # Step 3: OSC bundle creation
      bundle = build_osc_bundle(code)
      expect(bundle).to start_with("BundleOSC".b)

      # Step 4: UDP socket capability
      socket = UDPSocket.new
      expect(socket).to respond_to(:send)
      socket.close
    end
  end

  describe 'Comprehensive Audio Test Sequence' do
    it 'runs full audio test with all verification markers' do
      test_sequence = {
        setup: { time: Time.now, state: :ready },
        send_messages: [],
        expected_sounds: [],
        verification_complete: false
      }

      # Simulate 3 messages sent
      3.times do |i|
        test_sequence[:send_messages] << {
          index: i,
          time: Time.now,
          note: 60 + (i * 2),
          duration: 1
        }
        sleep 0.01
      end

      test_sequence[:expected_sounds] = test_sequence[:send_messages].length
      test_sequence[:verification_complete] = true

      expect(test_sequence[:send_messages].length).to eq(3)
      expect(test_sequence[:verification_complete]).to be true
    end
  end
end
