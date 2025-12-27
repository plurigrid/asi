#!/usr/bin/env ruby
# bin/god_mode_repl.rb
require 'socket'
require_relative '../lib/pitch_class'
require_relative '../lib/chord'

def encode_osc(address, *args)
  msg = address.b
  msg << "\x00" * (4 - (msg.length % 4))
  types = ","
  args.each { |arg| types << (arg.is_a?(Integer) ? "i" : "s") }
  msg << types.b
  msg << "\x00" * (4 - (types.length % 4))
  args.each do |arg|
    if arg.is_a?(Integer)
      msg << [arg].pack("N")
    else
      s = arg.b + "\x00"
      s << "\x00" * ((4 - (s.length % 4)) % 4)
      msg << s
    end
  end
  msg
end

PORT = 37457 # Discovered dynamically from process list
SOCKET = UDPSocket.new

def play_in_sonic_pi(code)
  packet = encode_osc("/run-code", "god-mode-repl", code)
  SOCKET.send(packet, 0, '127.0.0.1', PORT)
end

puts "🎵 MUSIC TOPOS: GOD MODE REPL"
puts "Blasting code directly to Sonic Pi port #{PORT}"
puts "Type notes (e.g. 'C E G') or 'quit'"

loop do
  print "> "
  input = gets
  break unless input
  input = input.chomp.strip
  break if input == 'quit'
  next if input.empty?

  begin
    notes = input.split.map { |n| PitchClass.from_name(n).to_midi(4) }
    code = "use_synth :prophet; play_chord #{notes.inspect}, release: 1.5, amp: 0.8"
    puts "  Blasting: #{code}"
    play_in_sonic_pi(code)
  rescue => e
    puts "  Error: #{e.message}"
  end
end
