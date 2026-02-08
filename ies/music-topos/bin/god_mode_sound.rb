#!/usr/bin/env ruby
# bin/god_mode_sound.rb
#
# BYPASSES LISTENERS
# Directly sends Ruby code to Sonic Pi's internal "Spider" server
# (Port 37457 as discovered via ps aux)

require 'socket'

def encode_osc(address, *args)
  msg = address.b
  msg << "\x00" * (4 - (msg.length % 4))
  types = ","
  args.each do |arg|
    case arg
    when Integer then types << "i"
    when String  then types << "s"
    end
  end
  msg << types.b
  msg << "\x00" * (4 - (types.length % 4))
  args.each do |arg|
    case arg
    when Integer then msg << [arg].pack("N")
    when String  then 
      s = arg.b + "\x00"
      s << "\x00" * ((4 - (s.length % 4)) % 4)
      msg << s
    end
  end
  msg
end

# DISCOVERED PORT FROM PS: 37457
# Logic: Sonic Pi launch args: spider-server.rb -u 37457 ...
# The first -u port is where it listens for code to run.
PORT = 37457 

puts "🚀 SENDING DIRECT CODE TO SONIC PI (PORT #{PORT})..."

# This is the actual code that will run inside Sonic Pi's engine
code = "use_synth :prophet; play_chord [60, 64, 67], release: 2, amp: 0.8"

begin
  socket = UDPSocket.new
  # Spider server expects a specific OSC address to run code
  packet = encode_osc("/run-code", "music-topos-god-mode", code)
  
  socket.send(packet, 0, '127.0.0.1', PORT)
  puts "✓ Code blasted to engine: #{code}"
  puts "You should hear sound NOW (no listener needed)."
rescue => e
  puts "✗ Error: #{e.message}"
end
