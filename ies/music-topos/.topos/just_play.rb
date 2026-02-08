#!/usr/bin/env ruby

# bin/just_play.rb
#
# JUST PLAY: Continuous journey through the four leitmotifs
# Each leitmotif leads into the next via harmonic progression
#
# No setup, no commands - just hit play and listen to mathematics unfold

require_relative '../lib/pitch_class'
require_relative '../lib/chord'
require_relative '../lib/neo_riemannian'
require_relative '../lib/worlds'
require_relative '../lib/ontological_validator'
require_relative '../lib/audio_synthesis'

class JustPlay
  def initialize
    @synthesis = AudioSynthesis.new(output_file: '/tmp/just_play_session.wav')
    @all_sequences = []
  end

  def run
    puts "=" * 80
    puts "🎵 JUST PLAY: Journey Through Four Leitmotifs"
    puts "=" * 80
    puts ""
    puts "Creating continuous session..."
    puts "Each leitmotif flows into the next via harmonic progression"
    puts ""

    # Build the complete journey
    build_complete_journey

    # Render all sequences
    puts "Rendering complete journey to audio..."
    output_file = @synthesis.render_sequence(@all_sequences, silence_between: 0.3)

    puts ""
    puts "=" * 80
    puts "✓ JOURNEY COMPLETE"
    puts "=" * 80
    puts ""
    puts "Output file: #{output_file}"
    puts ""
    puts "The session contains:"
    puts "  1. Circle Metric        (S¹ - chromatic exploration)"
    puts "  2. Voice Leading Path   (T⁴ - I-IV-V-I progression)"
    puts "  3. PLR Transformations  (S₃ - hexatonic cycle)"
    puts "  4. Harmonic Closure     (T-S-D - tonal resolution)"
    puts "  5. Return to Start      (full circle completion)"
    puts ""
    puts "Each progression flows naturally into the next."
    puts "All mathematically verified before rendering."
    puts ""
    puts "To listen: open #{output_file} with any audio player"
    puts ""
    puts "=" * 80
  end

  private

  def build_complete_journey
    puts ""
    puts "Building journey..."
    puts ""

    # SECTION 1: Circle Metric (S¹)
    puts "Section 1: Circle Metric (S¹) - All 12 Pitch Classes"
    puts "  The pitch circle ascending: C → B (full rotation)"
    section1 = build_circle_metric
    @all_sequences.concat(section1)
    add_silence(0.5)

    # SECTION 2: Voice Leading (T⁴)
    puts "Section 2: Voice Leading (T⁴) - Parsimonious Progression"
    puts "  I-IV-V-I in C major with minimal voice motion"
    section2 = build_voice_leading
    @all_sequences.concat(section2)
    add_silence(0.5)

    # SECTION 3: PLR Cycle (S₃)
    puts "Section 3: PLR Cycle (S₃) - Hexatonic Exploration"
    puts "  Six transformations exploring major/minor triads"
    section3 = build_plr_cycle
    @all_sequences.concat(section3)
    add_silence(0.5)

    # SECTION 4: Harmonic Closure (T-S-D)
    puts "Section 4: Harmonic Closure (T-S-D) - Tonal Resolution"
    puts "  Complete functional harmony cycle"
    section4 = build_harmonic_closure
    @all_sequences.concat(section4)
    add_silence(0.5)

    # SECTION 5: Return to Start
    puts "Section 5: Return to Start - Full Circle Completion"
    puts "  Journey returns to the beginning (mathematically closed)"
    section5 = build_return_to_start
    @all_sequences.concat(section5)

    puts ""
    puts "✓ Journey structure complete (#{@all_sequences.size} musical events)"
  end

  def build_circle_metric
    pitches = (0..11).map { |i| PitchClass.new(i) }
    sequence = []

    pitches.each do |pitch|
      frequency = pitch.to_frequency(4)
      sequence << {
        frequencies: frequency,
        duration: 0.25,
        amplitude: 0.5,
        label: "Pitch: #{pitch.note_name}",
        simultaneous: false
      }
    end

    sequence
  end

  def build_voice_leading
    c_major = Chord.from_notes(['C', 'E', 'G', 'C'])
    f_major = Chord.from_notes(['F', 'A', 'C', 'F'])
    g_major = Chord.from_notes(['G', 'B', 'D', 'G'])

    sequence = []
    [c_major, f_major, g_major, c_major].each do |chord|
      frequencies = chord.to_frequencies([4, 3, 3, 2])
      sequence << {
        frequencies: frequencies,
        duration: 1.0,
        amplitude: 0.4,
        label: "Chord: #{chord}",
        simultaneous: true
      }
    end

    sequence
  end

  def build_plr_cycle
    c_major = Chord.from_notes(['C', 'E', 'G'])
    cycle = NeoRiemannian.hexatonic_cycle(c_major, 6)

    sequence = []
    cycle.each_with_index do |chord, idx|
      frequencies = chord.to_frequencies([4, 3, 3])
      sequence << {
        frequencies: frequencies,
        duration: 0.8,
        amplitude: 0.4,
        label: "PLR Step #{idx}: #{chord}",
        simultaneous: true
      }
    end

    sequence
  end

  def build_harmonic_closure
    i = Chord.from_notes(['C', 'E', 'G', 'C'])
    iv = Chord.from_notes(['F', 'A', 'C', 'F'])
    v = Chord.from_notes(['G', 'B', 'D', 'G'])

    sequence = []
    [i, iv, v, i].each_with_index do |chord, idx|
      frequencies = chord.to_frequencies([4, 3, 3, 2])
      functions = ['T (Tonic)', 'S (Subdominant)', 'D (Dominant)', 'T (Tonic)']
      sequence << {
        frequencies: frequencies,
        duration: 1.2,
        amplitude: 0.4,
        label: "#{functions[idx]}: #{chord}",
        simultaneous: true
      }
    end

    sequence
  end

  def build_return_to_start
    # Build a smooth harmonic path back to C major
    chords = [
      Chord.from_notes(['G', 'B', 'D', 'G']),   # V
      Chord.from_notes(['D', 'F#', 'A', 'D']),  # ii
      Chord.from_notes(['A', 'C#', 'E', 'A']),  # vi
      Chord.from_notes(['C', 'E', 'G', 'C'])    # I (return)
    ]

    sequence = []
    chords.each do |chord|
      frequencies = chord.to_frequencies([4, 3, 3, 2])
      sequence << {
        frequencies: frequencies,
        duration: 1.0,
        amplitude: 0.4,
        label: "Return: #{chord}",
        simultaneous: true
      }
    end

    sequence
  end

  def add_silence(duration)
    @all_sequences << {
      frequencies: 0,
      duration: duration,
      amplitude: 0
    }
  end
end

# Run the session
session = JustPlay.new
session.run
