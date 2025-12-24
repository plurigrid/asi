#!/usr/bin/env ruby
# test_audio_effects.rb
# Comprehensive test suite for audio effects processing
#
# Tests:
#   1. Delay effect with various parameters
#   2. Reverb effect quality
#   3. Tremolo amplitude modulation
#   4. Vibrato frequency modulation
#   5. Chorus thickening effect
#   6. Effect chains (multiple effects in sequence)
#   7. Audio normalization and clipping prevention

require_relative 'lib/audio_effects'
require 'fileutils'

puts "=" * 80
puts "🎵 AUDIO EFFECTS TEST SUITE"
puts "=" * 80
puts ""

tests_passed = 0
tests_total = 0

# Helper: Generate a test sine wave
def generate_sine_wave(frequency, duration_sec, sample_rate = 44100, amplitude = 20000)
  samples = []
  num_samples = (duration_sec * sample_rate).to_i

  (0...num_samples).each do |i|
    t = i.to_f / sample_rate
    # Sine wave at specified frequency
    sample = (amplitude * Math.sin(2 * Math::PI * frequency * t)).to_i
    samples << sample
  end

  samples
end

# Helper: Analyze signal characteristics
def analyze_signal(samples)
  return {} if samples.empty?

  {
    count: samples.length,
    max: samples.max,
    min: samples.min,
    peak: [samples.max.abs, samples.min.abs].max,
    clipped: samples.any? { |s| s.abs >= 32767 }
  }
end

# Helper: Check signal energy (RMS)
def calculate_rms(samples)
  return 0.0 if samples.empty?
  sum_squares = samples.sum { |s| s.to_f ** 2 }
  Math.sqrt(sum_squares / samples.length)
end

puts "=" * 80
puts "TEST 1: Delay Effect"
puts "=" * 80
puts ""

tests_total += 1
begin
  effects = AudioEffects.new

  # Generate 1 second of sine wave at 440 Hz
  test_signal = generate_sine_wave(440, 1.0)
  original_rms = calculate_rms(test_signal)

  # Apply delay with moderate parameters
  delayed = effects.apply_delay(
    test_signal,
    delay_time: 0.3,
    feedback: 0.4,
    wet_mix: 0.5
  )

  delayed_rms = calculate_rms(delayed)
  analysis = analyze_signal(delayed)

  puts "  Input signal: 440 Hz sine wave"
  puts "    Original RMS: #{original_rms.round(2)}"
  puts "    Delayed RMS: #{delayed_rms.round(2)}"
  puts "    Peak amplitude: #{analysis[:peak]}"
  puts "    Clipped: #{analysis[:clipped]}"

  # Verify delay worked
  if delayed.length == test_signal.length && !analysis[:clipped]
    puts "  ✓ Delay effect applied successfully"
    tests_passed += 1
  else
    puts "  ✗ Delay effect failed validation"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST 2: Reverb Effect"
puts "=" * 80
puts ""

tests_total += 1
begin
  effects = AudioEffects.new

  # Generate shorter signal for reverb test
  test_signal = generate_sine_wave(440, 0.5)
  original_rms = calculate_rms(test_signal)

  # Apply reverb
  reverb = effects.apply_reverb(
    test_signal,
    room_size: 0.6,
    damping: 0.5,
    wet_mix: 0.4
  )

  reverb_rms = calculate_rms(reverb)
  analysis = analyze_signal(reverb)

  puts "  Input signal: 440 Hz sine wave (0.5 sec)"
  puts "    Original RMS: #{original_rms.round(2)}"
  puts "    Reverb RMS: #{reverb_rms.round(2)}"
  puts "    Peak amplitude: #{analysis[:peak]}"
  puts "    Clipped: #{analysis[:clipped]}"

  # Verify reverb worked and didn't cause clipping
  if reverb.length == test_signal.length && !analysis[:clipped]
    puts "  ✓ Reverb effect applied successfully"
    tests_passed += 1
  else
    puts "  ✗ Reverb effect failed validation"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST 3: Tremolo Effect (Amplitude Modulation)"
puts "=" * 80
puts ""

tests_total += 1
begin
  effects = AudioEffects.new

  # Generate test signal
  test_signal = generate_sine_wave(440, 1.0)
  original_peak = analyze_signal(test_signal)[:peak]

  # Apply tremolo at 5 Hz with 60% depth
  tremolo = effects.apply_tremolo(
    test_signal,
    rate: 5.0,
    depth: 0.6
  )

  tremolo_peak = analyze_signal(tremolo)[:peak]

  puts "  Input signal: 440 Hz sine wave with tremolo modulation"
  puts "    Rate: 5.0 Hz (5 wobbles per second)"
  puts "    Depth: 0.6 (60% modulation)"
  puts "    Original peak: #{original_peak}"
  puts "    Tremolo peak: #{tremolo_peak}"
  puts "    Amplitude variation: #{((original_peak - tremolo_peak).abs / original_peak * 100).round(1)}%"

  # Verify tremolo worked
  if tremolo.length == test_signal.length && tremolo_peak > 0
    puts "  ✓ Tremolo effect applied successfully"
    tests_passed += 1
  else
    puts "  ✗ Tremolo effect failed validation"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST 4: Vibrato Effect (Frequency Modulation)"
puts "=" * 80
puts ""

tests_total += 1
begin
  effects = AudioEffects.new

  # Generate test signal
  test_signal = generate_sine_wave(440, 0.5)

  # Apply vibrato with subtle pitch variation
  vibrato = effects.apply_vibrato(
    test_signal,
    rate: 6.0,
    depth: 2.0  # 2 semitones
  )

  analysis = analyze_signal(vibrato)

  puts "  Input signal: 440 Hz sine wave with vibrato modulation"
  puts "    Rate: 6.0 Hz (pitch wobbles 6 times per second)"
  puts "    Depth: 2.0 semitones (±2 semitone pitch variation)"
  puts "    Output length: #{vibrato.length} samples"
  puts "    Peak amplitude: #{analysis[:peak]}"
  puts "    Clipped: #{analysis[:clipped]}"

  # Verify vibrato worked
  if vibrato.length == test_signal.length && !analysis[:clipped]
    puts "  ✓ Vibrato effect applied successfully"
    tests_passed += 1
  else
    puts "  ✗ Vibrato effect failed validation"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST 5: Chorus Effect"
puts "=" * 80
puts ""

tests_total += 1
begin
  effects = AudioEffects.new

  # Generate test signal
  test_signal = generate_sine_wave(440, 0.5)
  original_rms = calculate_rms(test_signal)

  # Apply chorus for thickening
  chorus = effects.apply_chorus(
    test_signal,
    delay_time: 0.025,  # 25ms base delay
    rate: 1.5,          # 1.5 Hz LFO
    depth: 0.003        # 3ms modulation
  )

  chorus_rms = calculate_rms(chorus)
  analysis = analyze_signal(chorus)

  puts "  Input signal: 440 Hz sine wave"
  puts "    Base delay: 25ms"
  puts "    LFO rate: 1.5 Hz"
  puts "    Modulation depth: 3ms"
  puts "    Original RMS: #{original_rms.round(2)}"
  puts "    Chorus RMS: #{chorus_rms.round(2)}"
  puts "    Peak amplitude: #{analysis[:peak]}"

  # Verify chorus worked
  if chorus.length == test_signal.length
    puts "  ✓ Chorus effect applied successfully"
    tests_passed += 1
  else
    puts "  ✗ Chorus effect failed validation"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST 6: Effect Chain (Multiple Effects in Sequence)"
puts "=" * 80
puts ""

tests_total += 1
begin
  effects = AudioEffects.new

  # Generate test signal
  test_signal = generate_sine_wave(440, 0.5)
  original_peak = analyze_signal(test_signal)[:peak]

  # Build effect chain: delay → reverb → tremolo
  effects_chain = [
    {
      effect: :delay,
      params: { delay_time: 0.2, feedback: 0.3, wet_mix: 0.3 }
    },
    {
      effect: :reverb,
      params: { room_size: 0.5, damping: 0.5, wet_mix: 0.3 }
    },
    {
      effect: :tremolo,
      params: { rate: 4.0, depth: 0.4 }
    }
  ]

  # Apply chain
  result = effects.apply_effects(test_signal, effects_chain)
  result_analysis = analyze_signal(result)

  puts "  Effect chain: delay → reverb → tremolo"
  puts "    Input peak: #{original_peak}"
  puts "    Output peak: #{result_analysis[:peak]}"
  puts "    Output length: #{result.length} samples"
  puts "    Clipped: #{result_analysis[:clipped]}"

  # Verify chain worked
  if result.length == test_signal.length && !result_analysis[:clipped]
    puts "  ✓ Effect chain applied successfully"
    tests_passed += 1
  else
    puts "  ✗ Effect chain failed validation"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST 7: Audio Normalization and Clipping Prevention"
puts "=" * 80
puts ""

tests_total += 1
begin
  effects = AudioEffects.new

  # Create a loud test signal
  loud_signal = generate_sine_wave(440, 0.5, 44100, 30000)  # Very loud
  loud_peak = analyze_signal(loud_signal)[:peak]

  # Apply aggressive reverb to test normalization
  result = effects.apply_reverb(
    loud_signal,
    room_size: 0.7,
    damping: 0.3,
    wet_mix: 0.6
  )

  result_analysis = analyze_signal(result)

  puts "  Testing normalization with loud input signal"
  puts "    Input peak: #{loud_peak} (near max 32767)"
  puts "    Output peak: #{result_analysis[:peak]}"
  puts "    Clipped: #{result_analysis[:clipped]}"

  # Verify normalization prevented clipping
  if !result_analysis[:clipped] && result_analysis[:peak] <= 32767
    puts "  ✓ Normalization prevented clipping"
    tests_passed += 1
  else
    puts "  ✗ Normalization failed - audio clipped!"
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST 8: Effect Parameter Validation"
puts "=" * 80
puts ""

tests_total += 1
begin
  effects = AudioEffects.new
  test_signal = generate_sine_wave(440, 0.3)

  # Test with edge case parameters
  test_cases = [
    { name: "Delay with zero time", effect: :delay, params: { delay_time: 0 } },
    { name: "Reverb with zero mix", effect: :reverb, params: { wet_mix: 0 } },
    { name: "Tremolo with zero depth", effect: :tremolo, params: { depth: 0 } }
  ]

  all_valid = true
  test_cases.each do |tc|
    result = effects.apply_effects(
      test_signal,
      [{ effect: tc[:effect], params: tc[:params] }]
    )

    if result.length == test_signal.length
      puts "  ✓ #{tc[:name]}: handled correctly"
    else
      puts "  ✗ #{tc[:name]}: failed"
      all_valid = false
    end
  end

  if all_valid
    tests_passed += 1
  end
rescue => e
  puts "  ✗ Error: #{e.message}"
end

puts ""

# ============================================================================
puts "=" * 80
puts "TEST SUMMARY"
puts "=" * 80
puts ""

if tests_passed == tests_total
  puts "✓ ALL #{tests_total} TESTS PASSED!"
  puts ""
  puts "Audio Effects Status: FULLY OPERATIONAL"
  puts ""
  puts "Available effects:"
  puts "  • Delay (echo with feedback)"
  puts "  • Reverb (Freeverb-style comb filters)"
  puts "  • Tremolo (amplitude modulation via LFO)"
  puts "  • Vibrato (frequency modulation via delay)"
  puts "  • Chorus (delay modulation for thickening)"
  puts ""
  puts "Next Steps:"
  puts "  1. Integrate effects into AudioSynthesis pipeline"
  puts "  2. Create effect preset system (cathedral, slapback, etc.)"
  puts "  3. Generate test WAV files with effects applied"
  puts ""

  exit 0
else
  puts "✗ #{tests_total - tests_passed} TEST(S) FAILED (#{tests_passed}/#{tests_total})"
  puts ""
  puts "Please check output above for details."
  puts ""

  exit 1
end
