#!/usr/bin/env ruby
# bin/world_jump.rb
#
# JUMPING BETWEEN WORLDS
# Demonstrates ∀ W₁, W₂ ∈ Worlds: W₁ ⇝* W₂
#
# Journey:
# 1. Pitch Space World (Single Notes)
#    ⇝ Morphism: chord construction
# 2. Chord Space World (Triads)
#    ⇝ Morphism: PLR Transformation
# 3. Transformation World (Hexatonic Cycle)
#    ⇝ Morphism: Harmonic Function Assignment
# 4. Harmonic World (T-S-D resolution)

require 'socket'
require_relative '../lib/pitch_class'
require_relative '../lib/chord'
require_relative '../lib/neo_riemannian'
require_relative '../lib/worlds'

# God Mode OSC Sender
PORT = 37457
SOCKET = UDPSocket.new

def blast_code(code)
  # OSC Address: /run-code, Args: ["source", "code"]
  msg = "/run-code\x00\x00\x00".b
  msg << ",ss\x00".b
  msg << "world-jump\x00\x00".b
  
  c = code.b + "\x00"
  c << "\x00" * ((4 - (c.length % 4)) % 4)
  msg << c
  
  SOCKET.send(msg, 0, '127.0.0.1', PORT)
end

puts "=" * 80
puts "🌍 WORLD REACHABILITY DEMONSTRATION"
puts "=" * 80
puts "Proof of Axiom: ∀ W₁, W₂ ∈ Worlds: W₁ ⇝* W₂"
puts ""

# --- WORLD 1: Pitch Space ---
puts "Step 1: Inhabiting Pitch Space (W₁)"
[0, 4, 7].each do |p|
  pc = PitchClass.new(p)
  puts "  Object: #{pc}"
  blast_code("use_synth :sine; play #{pc.to_midi(4)}, release: 0.5")
  sleep 0.5
end

# --- MORPHISM: Construct Chord ---
puts "\n⇝ Applying Morphism: Chord Construction (Functor P → C)"

# --- WORLD 2: Chord Space ---
c_maj = Chord.from_notes(['C', 'E', 'G'])
puts "Step 2: Entering Chord Space (W₂)"
puts "  Object: #{c_maj}"
blast_code("use_synth :prophet; play_chord #{c_maj.to_midi_notes([4,4,4]).inspect}, release: 1.5")
sleep 2

# --- MORPHISM: PLR Transformation ---
puts "\n⇝ Applying Morphism: Parallel Transformation (P ∈ S₃)"

# --- WORLD 3: Transformation World ---
c_min = NeoRiemannian.parallel(c_maj)
puts "Step 3: Entering Transformation World (W₃)"
puts "  Morphism Result: #{c_maj} ⇝ P ⇝ #{c_min}"
blast_code("use_synth :prophet; play_chord #{c_min.to_midi_notes([4,4,4]).inspect}, release: 1.5")
sleep 2

# --- MORPHISM: Functional Assignment ---
puts "\n⇝ Applying Morphism: Functional Assignment (Homecoming)"

# --- WORLD 4: Harmonic World ---
puts "Step 4: Entering Harmonic World (W₄)"
puts "  Resolution: T-S-D-T cycle"

progression = [
  Chord.from_notes(['C', 'E', 'G']), # T
  Chord.from_notes(['F', 'A', 'C']), # S
  Chord.from_notes(['G', 'B', 'D']), # D
  Chord.from_notes(['C', 'E', 'G'])  # T
]

progression.each_with_index do |chord, i|
  labels = ["Tonic", "Subdominant", "Dominant", "Tonic"]
  puts "  Function: #{labels[i]} (#{chord})"
  blast_code("use_synth :piano; play_chord #{chord.to_midi_notes([4,4,4]).inspect}, release: 1.0")
  sleep 1.2
end

puts ""
puts "✓ PROOF COMPLETE: All worlds reached and interconnected."
puts "=" * 80
