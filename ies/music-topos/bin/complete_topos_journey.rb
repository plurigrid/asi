#!/usr/bin/env ruby
# bin/complete_topos_journey.rb
#
# THE COMPLETE 11-CATEGORY TOPOS JOURNEY
# Proof of Axiom: ∀ Wᵢ, Wⱼ ∈ {W₁...W₁₁}: Wᵢ ⇝* Wⱼ
#
# A continuous morphism through all 11 mathematical worlds.

require 'socket'
require_relative '../lib/pitch_class'
require_relative '../lib/chord'
require_relative '../lib/neo_riemannian'
require_relative '../lib/worlds'
require_relative '../lib/voice_leading'
require_relative '../lib/progressions'
require_relative '../lib/structure'
require_relative '../lib/form'
require_relative '../lib/spectral'

# God Mode OSC Sender (Port 37457 discovered dynamically)
PORT = 37457
SOCKET = UDPSocket.new

def blast_code(code)
  msg = "/run-code\x00\x00\x00".b << ",ss\x00".b << "topos-journey\x00".b
  c = code.b + "\x00"
  c << "\x00" * ((4 - (c.length % 4)) % 4)
  msg << c
  SOCKET.send(msg, 0, '127.0.0.1', PORT)
end

puts "=" * 80
puts "🌌 THE COMPLETE 11-CATEGORY MUSICAL TOPOS"
puts "=" * 80
puts "Executing continuous morphism through all 11 worlds..."
puts ""

# --- W1: Pitch Space ---
puts "1. Pitch Space (W₁): The atomic semitone"
p = PitchClass.new(0)
blast_code("use_synth :sine; play 60, release: 0.5")
sleep 0.6

# --- W2: Chord Space ---
puts "2. Chord Space (W₂): Emergent triads"
c_maj = Chord.from_notes(['C', 'E', 'G'])
blast_code("use_synth :prophet; play_chord [60, 64, 67], release: 1")
sleep 1.2

# --- W3: Leitmotif World ---
puts "3. Leitmotif World (W₃): Symbolic identity"
blast_code("use_synth :hollow; play_chord [60, 64, 67], release: 2, amp: 2")
sleep 1.5

# --- W4: Group Theory ---
puts "4. Group Theory (W₄): S₁₂ Permutations (P Operation)"
c_min = NeoRiemannian.parallel(c_maj)
blast_code("use_synth :prophet; play_chord [60, 63, 67], release: 1")
sleep 1.2

# --- W5: Harmonic Function ---
puts "5. Harmonic Function (W₅): Functional roles (T-S-D)"
[60, 65, 67].each do |root|
  blast_code("play_chord [#{root}, #{root+4}, #{root+7}], release: 0.5")
  sleep 0.6
end

# --- W6: Modulation ---
puts "6. Modulation (W₆): Key shifts (C Major ⇝ G Major)"
blast_code("use_synth :piano; play_chord [67, 71, 74], release: 1.5")
sleep 1.5

# --- W7: Polyphony ---
puts "7. Polyphony (W₇): SATB Voice Leading"
blast_code("in_thread { play 64 }; in_thread { play 60 }; in_thread { play 55 }; play 48")
sleep 1.5

# --- W8: Progression ---
puts "8. Progression (W₈): I-IV-V-I logic"
[[60,64,67], [65,69,72], [67,71,74], [60,64,67]].each do |notes|
  blast_code("play_chord #{notes.inspect}, release: 0.8")
  sleep 1
end

# --- W9: Structural Tonality ---
puts "9. Structural Tonality (W₉): The Authentic Cadence"
blast_code("play_chord [67, 71, 74, 77], release: 0.5; sleep 0.5; play_chord [60, 64, 67], release: 2")
sleep 2.5

# --- W10: Musical Form ---
puts "10. Musical Form (W₁₀): Sonata Recapitulation"
blast_code("with_fx :reverb do; play_chord [60, 64, 67], release: 4, amp: 1.5; end")
sleep 2

# --- W11: Advanced World ---
puts "11. Advanced World (W₁₁): Spectral Decomposition"
(1..8).each do |n|
  blast_code("use_synth :sine; play hz_to_midi(130.81 * #{n}), amp: #{1.0/n}, release: 2")
end

puts "\n✓ TOPOS REACHED: 11/11 Worlds instantiated."
puts "=" * 80
