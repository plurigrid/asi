#!/usr/bin/env ruby
# bin/leitmotif_evolution.rb
#
# LEITMOTIF EVOLUTION: Hear the core theme transform through harmonic functions
# Demonstrates: T → S → D → T cycle as audible phenomena

puts "=" * 80
puts "🎵 LEITMOTIF EVOLUTION: Harmonic Transformation in Real-Time"
puts "=" * 80
puts ""

# Generate WAV file with leitmotif evolution
def generate_leitmotif_wav(filename, transformations = [])
  File.open(filename, 'wb') do |f|
    sample_rate = 44100
    total_samples = transformations.sum { |t| (sample_rate * t[:duration]).to_i }

    # WAV header
    byte_rate = sample_rate * 2
    subchunk2_size = total_samples * 2
    chunk_size = 36 + subchunk2_size

    f.write('RIFF')
    f.write([chunk_size].pack('V'))
    f.write('WAVE')
    f.write('fmt ')
    f.write([16].pack('V'))
    f.write([1].pack('v'))
    f.write([1].pack('v'))
    f.write([sample_rate].pack('V'))
    f.write([byte_rate].pack('V'))
    f.write([2].pack('v'))
    f.write([16].pack('v'))
    f.write('data')
    f.write([subchunk2_size].pack('V'))

    # Generate transformations
    transformations.each do |transform|
      chord_samples = (sample_rate * transform[:duration]).to_i
      chord_samples.times do |i|
        sample = 0.0
        transform[:frequencies].each do |freq|
          sample += Math.sin(2 * Math::PI * freq * i / sample_rate) * 0.25
        end
        pcm_value = (sample * 32767).to_i
        f.write([pcm_value].pack('s<'))
      end
    end
  end
end

# THE CORE LEITMOTIF: C Major chord (262, 330, 392 Hz)
core_leitmotif = [262, 330, 392]  # C-E-G (TONIC)

puts "LEITMOTIF TRANSFORMATIONS:"
puts "━" * 80
puts ""

# Phase 1: Tonic (Home)
puts "1️⃣  TONIC (T): Home State"
puts "   Frequencies: #{core_leitmotif.join(', ')} Hz (C Major triad)"
puts "   Function: STABLE, at rest, identity"
puts "   Harmonic meaning: 'I am the home.'"
puts ""

# Phase 2: Modulation to Subdominant (S)
subdominant = [349, 440, 523]  # F-A-C (IV, the SUBDOMINANT function)
puts "2️⃣  SUBDOMINANT (S): Preparation"
puts "   Frequencies: #{subdominant.join(', ')} Hz (F Major triad)"
puts "   Function: MOVING, building tension, leaving home"
puts "   Harmonic meaning: 'I prepare to move away.'"
puts "   Distance from Tonic: #{subdominant[0] - core_leitmotif[0]} semitones"
puts ""

# Phase 3: Dominant (D)
dominant = [392, 494, 587]  # G-B-D (V, the DOMINANT function)
puts "3️⃣  DOMINANT (D): Maximum Tension"
puts "   Frequencies: #{dominant.join(', ')} Hz (G Major triad)"
puts "   Function: TENSION, expectation, drive to resolve"
puts "   Harmonic meaning: 'I need to return.'"
puts "   Distance from Tonic: #{dominant[0] - core_leitmotif[0]} semitones (perfect 5th)"
puts ""

# Phase 4: Resolution back to Tonic (T)
puts "4️⃣  RETURN TO TONIC (T): Resolution"
puts "   Frequencies: #{core_leitmotif.join(', ')} Hz (C Major triad)"
puts "   Function: STABILITY RESTORED, closure achieved"
puts "   Harmonic meaning: 'Home again. Complete.'"
puts ""

# Generate the leitmotif evolution WAV file
puts "=" * 80
puts "GENERATING AUDIO FILE..."
puts "=" * 80
puts ""

transformations = [
  { frequencies: core_leitmotif,     name: "TONIC (T)",       duration: 2.0 },
  { frequencies: subdominant,        name: "SUBDOMINANT (S)", duration: 2.0 },
  { frequencies: dominant,           name: "DOMINANT (D)",    duration: 2.0 },
  { frequencies: core_leitmotif,     name: "RETURN TO T",     duration: 3.0 }
]

filename = '/tmp/leitmotif_evolution.wav'
generate_leitmotif_wav(filename, transformations)

puts "✓ Generated: #{filename}"
puts "  Total duration: 9 seconds"
puts "  T (2s) → S (2s) → D (2s) → T (3s)"
puts ""

puts "PLAYING LEITMOTIF EVOLUTION..."
puts "Listen for:"
puts "  • PHASE 1 (T):  Stable C Major chord - home base"
puts "  • PHASE 2 (S):  Shift to F Major - moving away"
puts "  • PHASE 3 (D):  Shift to G Major - tension increases"
puts "  • PHASE 4 (T):  Return to C Major - closure achieved"
puts ""

system("afplay #{filename}")

puts ""
puts "=" * 80
puts "✅ LEITMOTIF EVOLUTION COMPLETE"
puts "=" * 80
puts ""
puts "What you heard:"
puts "  • The same THEME in 4 harmonic contexts"
puts "  • Each transformation serving a FUNCTION in the cycle T→S→D→T"
puts "  • The JOURNEY of music: leaving home, building tension, returning"
puts ""
puts "This is the ESSENCE of tonality:"
puts "  - Tonic is IDENTITY (who we are)"
puts "  - Subdominant is PREPARATION (getting ready to move)"
puts "  - Dominant is TENSION (the moment of change)"
puts "  - Return to Tonic is CLOSURE (we arrive)"
puts ""
puts "Every piece of tonal music tells this story."
puts "Now you've HEARD it."
puts ""
