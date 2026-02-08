#!/usr/bin/env ruby
# bin/sound_now.rb
#
# IMMEDIATE SOUND TEST
# Plays a single C Major chord via OSC to Sonic Pi
# Bypasses all REPL/Interaction layers for immediate gratification

require 'socket'
require_relative '../lib/sonic_pi_renderer'
require_relative '../lib/chord'
require_relative '../lib/pitch_class'

puts "=" * 80
puts "🔊 SENDING SOUND TO SONIC PI NOW"
puts "=" * 80
puts ""

begin
  renderer = SonicPiRenderer.new(use_osc: true)
  
  # C Major Triad: C4, E4, G4
  chord = Chord.from_notes(['C', 'E', 'G'])
  
  puts "Sending OSC message for: #{chord}"
  puts "Port: 4559"
  
  # Play chord
  renderer.play_chord(chord, [4, 4, 4], 2.0)
  
  puts ""
  puts "✓ Message sent!"
  puts ""
  puts "If you don't hear anything:"
  puts "1. Ensure Sonic Pi is running"
  puts "2. Check Sonic Pi Prefs > IO > Enable OSC Server (Port 4559)"
  puts "3. Paste listener code into Sonic Pi (see README)"
  
rescue => e
  puts "✗ Error: #{e.message}"
end
