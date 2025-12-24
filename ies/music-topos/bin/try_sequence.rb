#!/usr/bin/env ruby
# bin/try_sequence.rb

require_relative '../lib/sonic_pi_renderer'
require_relative '../lib/pitch_class'

puts "🎵 Trying a C Major Scale..."
renderer = SonicPiRenderer.new(use_osc: true)

# C Major Scale: 0, 2, 4, 5, 7, 9, 11, 12
scale = [0, 2, 4, 5, 7, 9, 11, 12]

scale.each do |pc_val|
  pc = PitchClass.new(pc_val)
  # Calculate octave based on whether we wrapped around (12 is C5)
  octave = pc_val >= 12 ? 5 : 4
  
  puts "  #{pc.note_name}#{octave}"
  renderer.play_pitch_class(pc, octave, 0.25)
  sleep 0.25
end

puts "✓ Done. Did you hear it?"
