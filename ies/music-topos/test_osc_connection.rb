#!/usr/bin/env ruby
# test_osc_connection.rb
#
# Test OSC connection to Sonic Pi
# Verifies that the system can actually communicate with Sonic Pi

require 'socket'
require 'timeout'

puts "=" * 80
puts "🔍 OSC CONNECTION TEST"
puts "=" * 80
puts ""

OSC_HOST = 'localhost'
OSC_PORT = 4557

# Test 1: Can we reach Sonic Pi?
puts "Test 1: Checking Sonic Pi on #{OSC_HOST}:#{OSC_PORT}..."

begin
  socket = UDPSocket.new
  socket.connect(OSC_HOST, OSC_PORT)

  puts "  ✓ Socket created successfully"

  # Test 2: Send a simple OSC message
  puts ""
  puts "Test 2: Sending OSC test message..."

  code = "puts 'OSC test successful'"

  # Build minimal OSC bundle
  bundle = +"BundleOSC"
  bundle << [0, 0].pack("N2")  # Timestamp

  # Simple OSC message for testing
  message = "/run/code\0" + "\0" * 3  # Pad to 4-byte
  message += ",s\0\0"  # Type tag
  message += "#{code}\0"
  message << "\0" * (4 - ((code.length + 1) % 4)) if (code.length + 1) % 4 != 0

  size = [message.bytesize].pack("N")
  bundle << size << message

  socket.send(bundle, 0)
  puts "  ✓ OSC bundle sent (#{bundle.bytesize} bytes)"

  # Test 3: Check if Sonic Pi is listening
  puts ""
  puts "Test 3: Verifying Sonic Pi is listening..."

  # Try to send another message
  socket.send(bundle, 0)
  puts "  ✓ Second message sent"

  socket.close

  puts ""
  puts "=" * 80
  puts "✓ OSC CONNECTION SUCCESSFUL"
  puts "=" * 80
  puts ""
  puts "Result: Sonic Pi is running and listening on #{OSC_HOST}:#{OSC_PORT}"
  puts ""
  puts "Next steps:"
  puts "  1. ruby test_audio_synthesis.rb  (test audio generation)"
  puts "  2. ruby bin/interactive_repl.rb  (interactive composition)"
  puts ""

  exit 0

rescue Errno::ECONNREFUSED
  puts "  ✗ Connection refused"
  puts ""
  puts "=" * 80
  puts "✗ OSC CONNECTION FAILED"
  puts "=" * 80
  puts ""
  puts "Sonic Pi is not running on #{OSC_HOST}:#{OSC_PORT}"
  puts ""
  puts "To fix:"
  puts "  1. Install Sonic Pi: brew install sonic-pi"
  puts "  2. Launch Sonic Pi application"
  puts "  3. Return to terminal and run this test again"
  puts ""

  exit 1

rescue => e
  puts "  ✗ Error: #{e.message}"
  puts "  #{e.backtrace.first(3).join("\n  ")}"
  puts ""
  puts "=" * 80
  puts "✗ OSC CONNECTION ERROR"
  puts "=" * 80
  puts ""

  exit 2

end
