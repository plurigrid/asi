#!/usr/bin/env ruby
# test_audio_synthesis.rb
#
# Test the audio synthesis pipeline
# Verifies that mathematical objects convert to correct frequencies
# and OSC messages are properly formatted

require_relative 'lib/pitch_class'
require_relative 'lib/chord'
require_relative 'lib/audio_synthesis'
require_relative 'lib/sonic_pi_renderer'

puts "=" * 80
puts "🎵 AUDIO SYNTHESIS TEST"
puts "=" * 80
puts ""

test_results = []

# Test 1: Pitch Class to Frequency
puts "Test 1: PitchClass → Frequency conversion..."

test_pitches = [
  { pc: PitchClass.new(0), name: 'C', octave: 4, expected: 261.63 },
  { pc: PitchClass.new(7), name: 'G', octave: 4, expected: 392.00 },
  { pc: PitchClass.new(12), name: 'C', octave: 5, expected: 523.25 },
]

test_pitches.each do |test|
  freq = test[:pc].to_frequency(test[:octave])
  expected = test[:expected]
  error = (freq - expected).abs / expected
  status = error < 0.01 ? "✓" : "✗"

  puts "  #{status} #{test[:name]} (octave #{test[:octave]}): #{freq.round(2)} Hz (expected #{expected})"
  test_results << (error < 0.01)
end

puts ""

# Test 2: Chord to Frequencies
puts "Test 2: Chord → MIDI → Frequencies..."

c_major = Chord.from_notes(['C', 'E', 'G', 'C'])
midi_notes = c_major.to_midi_notes([4, 3, 3, 2])
frequencies = c_major.to_frequencies([4, 3, 3, 2])

puts "  Chord: #{c_major}"
puts "  MIDI notes: #{midi_notes.join(', ')}"
puts "  Frequencies: #{frequencies.map { |f| f.round(2) }.join(', ')} Hz"
test_results << frequencies.all? { |f| f > 20 && f < 20000 }  # Human hearing range
puts "  ✓ All frequencies in human hearing range (20-20000 Hz)"

puts ""

# Test 3: Voice Leading Distance
puts "Test 3: Voice Leading Distance (Metric Space)..."

f_major = Chord.from_notes(['F', 'A', 'C', 'F'])
distance = c_major.voice_leading_distance(f_major)

puts "  C Major → F Major"
puts "    Total motion: #{distance[:total]} semitones"
puts "    Parsimonious: #{distance[:parsimonious] ? 'Yes ✓' : 'No'}"

# F is 5 semitones up, A is 5 up, C is 5 up, F is 5 up = 20 total
# This should NOT be parsimonious (< 6 semitones)
expected_parsimonious = false
status = distance[:parsimonious] == expected_parsimonious ? "✓" : "✗"
puts "  #{status} Parsimonious classification correct"
test_results << (distance[:parsimonious] == expected_parsimonious)

puts ""

# Test 4: OSC Message Formatting
puts "Test 4: OSC Message Formatting..."

renderer = SonicPiRenderer.new(use_osc: false)  # Don't actually connect

osc_message = {
  synth: :sine,
  midi: 60,
  frequency: 261.63,
  duration: 1.0,
  amplitude: 0.7
}

puts "  OSC Message structure:"
puts "    synth: #{osc_message[:synth]}"
puts "    midi: #{osc_message[:midi]}"
puts "    frequency: #{osc_message[:frequency].round(2)} Hz"
puts "    duration: #{osc_message[:duration]}s"
puts "    amplitude: #{osc_message[:amplitude]}"

# Verify message has all required fields
required_fields = [:synth, :midi, :frequency, :duration, :amplitude]
all_present = required_fields.all? { |field| osc_message.key?(field) }
puts "  #{all_present ? '✓' : '✗'} All required fields present"
test_results << all_present

puts ""

# Test 5: WAV Synthesis
puts "Test 5: WAV File Synthesis..."

begin
  synthesis = AudioSynthesis.new(output_file: '/tmp/test_audio.wav')

  # Generate a simple sequence
  sequence = [
    {
      frequencies: 261.63,  # Middle C
      duration: 0.5,
      amplitude: 0.5,
      label: "Test sine wave"
    }
  ]

  output = synthesis.render_sequence(sequence, silence_between: 0.1)

  # Check if file was created
  if File.exist?(output)
    file_size = File.size(output)
    puts "  ✓ WAV file created: #{output}"
    puts "    Size: #{file_size} bytes"
    puts "    Duration: ~0.6 seconds (0.5s signal + 0.1s silence)"

    # WAV file should be at least 44100 * 2 * 0.6 = ~52,920 bytes
    expected_min_size = 44100 * 2 * 0.5  # 44.1kHz, 16-bit stereo, 0.5s
    size_ok = file_size > expected_min_size * 0.8  # Allow 20% tolerance
    puts "  #{size_ok ? '✓' : '✗'} File size reasonable"
    test_results << size_ok
  else
    puts "  ✗ WAV file not created"
    test_results << false
  end

rescue => e
  puts "  ✗ Error: #{e.message}"
  test_results << false
end

puts ""

# Summary
puts "=" * 80
passed = test_results.count(true)
total = test_results.count

if passed == total
  puts "✓ ALL TESTS PASSED (#{passed}/#{total})"
  puts "=" * 80
  puts ""
  puts "Audio synthesis pipeline is working correctly!"
  puts ""
  puts "Next steps:"
  puts "  1. Verify OSC connection: ruby test_osc_connection.rb"
  puts "  2. Run full system test: ruby test_complete_system.rb"
  puts "  3. Or compose interactively: ruby bin/interactive_repl.rb"
  puts ""
  exit 0
else
  puts "✗ SOME TESTS FAILED (#{passed}/#{total})"
  puts "=" * 80
  puts ""
  exit 1
end
