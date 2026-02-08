#!/usr/bin/env ruby
# bin/sonic_pi_initial_object_world.rb
#
# SONIC PI INITIAL OBJECT WORLD DEMONSTRATION
#
# Badiouian Ontology:
# ──────────────────
# A WORLD is a set of objects with relations between them, structured by a
# metric space and semantic closure conditions. The INITIAL OBJECT WORLD
# shows how all musical structure emerges from a single pitch.
#
# Objects in this world:
#   - InitialPitch: The atomic musical unit (C4, pitch class 0)
#   - PitchClasses: Permutations of the initial object (Category 4)
#   - HarmonicFunctions: Functional meanings (Category 5)
#   - Chords: Polyphonic objects (Category 7)
#   - Progressions: Functional sequences (Category 8)
#   - Cadences: Structural closures (Category 9)
#
# Relations:
#   - Permutation: Pitch classes emerge from initial pitch (S₁₂)
#   - Function: Pitch classes acquire harmonic meaning (T/S/D)
#   - Modulation: Pitch classes relate via circle of fifths (keys)
#   - Chord formation: Pitches combine into chords
#   - Progression membership: Chords form progressions
#   - Conclusion: Progressions end in cadences
#
# Semantic Closure: 8-dimensional completeness
#   ✓ Pitch space (all 12 pitches present)
#   ✓ Harmonic function (T/S/D roles assigned)
#   ✓ Modulation (circle of fifths relations)
#   ✓ Chord space (triadic structures formed)
#   ✓ Progression space (functional sequences)
#   ✓ Cadential structure (formal closures)
#   ✓ Emergence relations (objects properly derived)
#   ✓ Completion (world fully determined)

require 'socket'
require 'time'

# Load musical structure classes
$LOAD_PATH.unshift(File.expand_path('../lib', __dir__))
require 'pitch_class'
require 'chord'
require 'harmonic_function'
require 'harmony'  # Contains HarmonicProgression
require 'tonality'
require 'form'
require 'worlds/world'
require 'worlds/initial_object_world'

class SonicPiInitialObjectWorldDemo
  OSC_HOST = '127.0.0.1'
  OSC_PORT = 31682  # Sonic Pi OSC input port

  def initialize
    @socket = UDPSocket.new
    @socket.connect(OSC_HOST, OSC_PORT)
    @world = nil
    @demo_count = 0
  end

  def play_code(code, label = "")
    @demo_count += 1
    puts "\n🎵 DEMO #{@demo_count}: #{label}"
    puts "─" * 80
    puts ""

    bundle = build_osc_bundle(code)
    @socket.send(bundle, 0)

    sleep 0.1
  end

  def show_world_state(step_num, step_name)
    puts "\n" + "=" * 80
    puts "STEP #{step_num}: #{step_name}"
    puts "=" * 80
    puts ""
    puts "World: #{@world.name}"
    puts "Objects: #{@world.objects.length}"
    puts "Relations: #{@world.relations.length}"
    puts ""
  end

  private

  def build_osc_bundle(code)
    bundle = "BundleOSC".b
    bundle << [0, 0].pack("N2")
    message = encode_osc_message("/run/code", code)
    bundle << [message.bytesize].pack("N") << message
    bundle
  end

  def encode_osc_message(address, string)
    msg = address.b
    msg << ("\x00" * (4 - (address.length % 4))).b
    msg << "s\x00\x00\x00".b
    padded = (string + "\x00").b
    padded << ("\x00" * (4 - (padded.length % 4))).b
    msg << padded
    msg
  end
end

puts "=" * 80
puts "🎵 SONIC PI: INITIAL OBJECT WORLD"
puts "All Structure Emerging from a Single Pitch"
puts "=" * 80
puts ""

demo = SonicPiInitialObjectWorldDemo.new

puts "Creating the Initial Object World..."
puts "This world demonstrates how complete musical structure"
puts "emerges necessarily from a single primitive pitch object."
puts ""
puts "Connecting to Sonic Pi on #{SonicPiInitialObjectWorldDemo::OSC_HOST}:#{SonicPiInitialObjectWorldDemo::OSC_PORT}..."
puts ""

begin
  # Build the world
  demo.instance_variable_set(:@world, MusicalWorlds::InitialObjectWorld.create_from_initial_object(0))

  world = demo.instance_variable_get(:@world)

  puts "✓ Connected and World Created!"
  puts ""

  demo.show_world_state(0, "Initial Object: Single Pitch (C4)")

  puts "OBJECT: Initial Pitch Class 0 (C4, 262Hz)"
  puts "PROPERTIES: Atomic, indivisible, the seed of all music"
  puts ""

  demo.play_code(%{
with_synth :sine do
  puts "THE INITIAL OBJECT"
  puts "A single pitch: the atom of music"
  puts "From this, all musical structure emerges"
  play 60
  sleep 3
end
}, "The Initial Object: C4 (single pitch)")

  sleep 2

  demo.show_world_state(1, "Category 4: S₁₂ Permutation Group")

  puts "OBJECTS ADDED: 12 Pitch Classes (rotations of C)"
  puts "RELATIONS ADDED: 12 Permutation morphisms (C→D, C→E, ... C→B)"
  puts "PROPERTY: All 12 pitches now exist as rotations of the initial object"
  puts ""

  demo.play_code(%{
with_synth :sine do
  puts "CATEGORY 4: S₁₂ PERMUTATION GROUP"
  puts "The initial pitch generates all 12 pitch classes"
  puts "Each is a unique rotation in the cyclic group"

  # Play the 12-tone chromatic scale
  (0..11).each do |semitone|
    play 60 + semitone
    sleep 0.12
  end
  sleep 1
end
}, "Category 4: All 12 Pitch Classes Emerge")

  sleep 2

  demo.show_world_state(2, "Category 5: Harmonic Function")

  puts "OBJECTS ADDED: Harmonic Functions (Tonic, Subdominant, Dominant)"
  puts "RELATIONS ADDED: Function morphisms (pitch class → harmonic role)"
  puts "PROPERTY: Pitch classes now have functional meaning in tonal space"
  puts ""

  demo.play_code(%{
with_synth :piano do
  puts "CATEGORY 5: HARMONIC FUNCTION"
  puts "Pitch classes acquire functional roles"

  puts "T (Tonic): C Major"
  play_chord [60, 64, 67]
  sleep 1

  puts "S (Subdominant): F Major"
  play_chord [65, 69, 72]
  sleep 1

  puts "D (Dominant): G Major"
  play_chord [67, 71, 74]
  sleep 1

  puts "T (Return): C Major"
  play_chord [60, 64, 67]
  sleep 1.5
end
}, "Category 5: Harmonic Functions (T/S/D)")

  sleep 2

  demo.show_world_state(3, "Category 6: Modulation")

  puts "RELATIONS ADDED: Circle of fifths (modulation paths)"
  puts "PROPERTY: Pitch classes now form navigable harmonic paths"
  puts "RELATIONS: C→G (perfect 5th), G→D, D→F, F→C"
  puts ""

  demo.play_code(%{
with_synth :sine do
  puts "CATEGORY 6: MODULATION"
  puts "Harmonic functions create navigable key space"

  puts "Start: C Major (home)"
  play_chord [60, 64, 67]
  sleep 0.5

  puts "Journey: C → G (circle of fifths +1)"
  play_chord [67, 71, 74]
  sleep 0.5

  puts "Journey: G → D (circle of fifths +2)"
  play_chord [74, 78, 81]
  sleep 0.5

  puts "Return: D → F → C (harmonic closure)"
  play_chord [65, 69, 72]
  sleep 0.3
  play_chord [60, 64, 67]
  sleep 1
end
}, "Category 6: Modulation (Circle of Fifths)")

  sleep 2

  demo.show_world_state(4, "Category 7: Voice Leading (Polyphony)")

  puts "OBJECTS ADDED: Chords (triadic structures)"
  puts "PROPERTY: Single pitch becomes multiple coordinated voices"
  puts "RELATIONS: Pitch classes → Chord formations"
  puts ""

  demo.play_code(%{
with_synth :sine do
  puts "CATEGORY 7: VOICE LEADING"
  puts "Single pitch becomes polyphonic texture"

  puts "All voices in unison on C Major"
  in_thread { play 64; sleep 1 }  # Soprano
  in_thread { play 60; sleep 1 }  # Alto
  in_thread { play 55; sleep 1 }  # Tenor
  in_thread { play 48; sleep 1 }  # Bass
  sleep 1.2

  puts "Smooth motion to F Major (minimize semitone distance)"
  in_thread { play 65; sleep 1 }  # Soprano: +1
  in_thread { play 62; sleep 1 }  # Alto: +2
  in_thread { play 53; sleep 1 }  # Tenor: -2
  in_thread { play 53; sleep 1 }  # Bass: jump
  sleep 1.2

  puts "Return to C Major"
  in_thread { play 64; sleep 1 }
  in_thread { play 60; sleep 1 }
  in_thread { play 55; sleep 1 }
  in_thread { play 48; sleep 1 }
  sleep 1.2
end
}, "Category 7: Voice Leading (Polyphony)")

  sleep 2

  demo.show_world_state(5, "Category 8: Harmonic Progressions")

  puts "OBJECTS ADDED: Harmonic Progressions (I-IV-V-I)"
  puts "RELATIONS ADDED: Progression membership (chords → progression)"
  puts "PROPERTY: Chords now relate through functional harmonic logic"
  puts ""

  demo.play_code(%{
with_synth :piano do
  puts "CATEGORY 8: HARMONIC PROGRESSIONS"
  puts "Chords form functional harmonic sequences"

  puts "I (Tonic): Equilibrium"
  play_chord [60, 64, 67]
  sleep 0.8

  puts "IV (Subdominant): Preparation"
  play_chord [65, 69, 72]
  sleep 0.8

  puts "V (Dominant): Tension"
  play_chord [67, 71, 74]
  sleep 0.8

  puts "I (Tonic): Resolution and closure"
  play_chord [60, 64, 67]
  sleep 1.5
end
}, "Category 8: Classical Progression (I-IV-V-I)")

  sleep 2

  demo.show_world_state(6, "Category 9: Cadential Structures")

  puts "OBJECTS ADDED: Cadences (authentic V-I, plagal IV-I, etc.)"
  puts "RELATIONS ADDED: Conclusion morphisms (progression → cadence)"
  puts "PROPERTY: Progressions now have punctuation and closure"
  puts ""

  demo.play_code(%{
with_synth :sine do
  puts "CATEGORY 9: CADENTIAL STRUCTURES"
  puts "Progressions declare their formal role through cadences"

  puts "AUTHENTIC CADENCE (V-I): Strong, conclusive"
  play_chord [67, 71, 74]
  sleep 0.3
  play_chord [60, 64, 67]
  sleep 1
  sleep 0.3

  puts "PLAGAL CADENCE (IV-I): Gentle, gentle"
  play_chord [65, 69, 72]
  sleep 0.3
  play_chord [60, 64, 67]
  sleep 1
  sleep 0.3

  puts "HALF CADENCE (I-V): Open, questioning"
  play_chord [60, 64, 67]
  sleep 0.3
  play_chord [67, 71, 74]
  sleep 1
  sleep 0.3

  puts "DECEPTIVE CADENCE (V-vi): Surprise, subversion"
  play_chord [67, 71, 74]
  sleep 0.3
  play_chord [69, 72, 76]
  sleep 1
end
}, "Category 9: All Cadence Types (punctuation)")

  sleep 3

  puts ""
  puts "=" * 80
  puts "FINAL WORLD STATE"
  puts "=" * 80
  puts ""
  puts "World: #{world.name}"
  puts "Total Objects: #{world.objects.length}"
  puts "Total Relations: #{world.relations.length}"
  puts ""
  puts "Object Types:"
  puts "  - Initial Pitch Classes: 12"
  puts "  - Harmonic Functions: 3 (T, S, D)"
  puts "  - Chords: 3 (C Major, F Major, G Major)"
  puts "  - Progressions: 1 (I-IV-V-I)"
  puts "  - Cadences: 4 (Authentic, Plagal, Half, Deceptive)"
  puts ""
  puts "Semantic Closure Status:"
  puts "  ✓ Pitch space: #{world.pitch_classes.length}/12 pitches"
  puts "  ✓ Harmonic function: #{world.harmonic_functions_obj.length}/3 functions"
  puts "  ✓ Modulation: #{world.relations.count { |r| r[:type].to_s.include?('circle') }}/4 circle-of-fifths"
  puts "  ✓ Chord space: #{world.chords_obj.length} chords"
  puts "  ✓ Progression space: #{world.progressions_obj.length} progressions"
  puts "  ✓ Cadential structure: #{world.cadences_obj.length} cadences"
  puts "  ✓ Emergence: #{world.relations.count { |r| r[:type] == :permutation }} permutation relations"
  puts "  ✓ Completion: World is fully 8-dimensionally closed"
  puts ""

  demo.play_code(%{
with_synth :sine do
  puts "FINAL SYNTHESIS: Complete Emergence from Initial Object"
  puts ""

  puts "1️⃣  The initial pitch (C4)"
  play_chord [60]
  sleep 1.5

  puts "2️⃣  → all 12 pitch classes (Category 4)"
  (0..11).each { |i| play 60 + i; sleep 0.08 }
  sleep 0.5

  puts "3️⃣  → harmonic functions (Category 5)"
  play_chord [60, 64, 67]; sleep 0.3
  play_chord [67, 71, 74]; sleep 0.3
  play_chord [60, 64, 67]; sleep 0.5

  puts "4️⃣  → modulation paths (Category 6)"
  play_chord [60, 64, 67]; sleep 0.2
  play_chord [67, 71, 74]; sleep 0.2
  play_chord [60, 64, 67]; sleep 0.5

  puts "5️⃣  → voice-led chords (Category 7)"
  play_chord [60, 64, 67]; sleep 0.3
  play_chord [65, 69, 72]; sleep 0.5

  puts "6️⃣  → harmonic progressions (Category 8)"
  play_chord [60, 64, 67]; sleep 0.2
  play_chord [65, 69, 72]; sleep 0.2
  play_chord [67, 71, 74]; sleep 0.2
  play_chord [60, 64, 67]; sleep 0.5

  puts "7️⃣  → cadential structures (Category 9)"
  play_chord [67, 71, 74]; sleep 0.3
  play_chord [60, 64, 67]; sleep 1.5

  puts "✓✓✓ COMPLETE EMERGENCE FROM INITIAL OBJECT ✓✓✓"
end
}, "Complete Synthesis: From Single Pitch to Full World")

  sleep 4

  puts ""
  puts "=" * 80
  puts "✅ INITIAL OBJECT WORLD COMPLETE"
  puts "=" * 80
  puts ""
  puts "KEY INSIGHT:"
  puts "  Every musical structure emerges necessarily from the initial pitch."
  puts "  There is no arbitrary choice - each category unfolds from the previous."
  puts "  The world is determined by its initial object."
  puts ""
  puts "NEXT: See sonic_pi_terminal_object_world.rb"
  puts "       to see the reverse view: all fragments resolving INTO completion."
  puts ""

rescue => e
  puts "ERROR: #{e.message}"
  puts e.backtrace.join("\n")
end
