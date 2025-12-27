#!/usr/bin/env ruby
# bin/arpeggio_blast.rb
require 'socket'

def send_osc(port, address, *args)
  client = UDPSocket.new
  client.connect('127.0.0.1', port)
  
  # Pad address
  msg = address.dup.b
  msg << "\x00" * (4 - (msg.length % 4))
  
  # Types
  types = ","
  args.each do |arg|
    case arg
    when Integer then types << "i"
    when Float   then types << "f"
    when String  then types << "s"
    end
  end
  msg << types.b
  msg << "\x00" * (4 - (types.length % 4))
  
  # Args
  args.each do |arg|
    case arg
    when Integer
      msg << [arg].pack("N")
    when Float
      msg << [arg].pack("g")
    when String
      s = arg.dup.b
      s << "\x00" * (4 - (s.length % 4))
      msg << s
    end
  end
  
  client.send(msg, 0)
  client.close
rescue => e
  puts "Error on port #{port}: #{e.message}"
end

puts "🎵 BLASTING ARPEGGIO TO PORTS 4559 AND 4560..."

# C Major Arpeggio: C4, E4, G4, C5
notes = [60, 64, 67, 72]

notes.each do |note|
  puts "  Note: #{note}"
  # Send to both common ports to be sure
  send_osc(4559, "/trigger/prophet", note, 0.2)
  send_osc(4560, "/trigger/prophet", note, 0.2)
  sleep 0.15
end

puts "✓ Done!"
