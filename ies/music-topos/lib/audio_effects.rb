# lib/audio_effects.rb
#
# Audio Effects Processing
# Adds reverb, delay, modulation to synthesized audio
#
# Effects:
#   - Delay: Time-shifted echo
#   - Reverb: Simple comb filter-based reverb
#   - Tremolo: Amplitude modulation (amplitude wobble)
#   - Vibrato: Frequency modulation (pitch wobble)
#   - Chorus: Slight delay modulation for thickening effect

class AudioEffects
  SAMPLE_RATE = 44100
  MAX_AMPLITUDE = 32767.0

  def initialize
    @sample_rate = SAMPLE_RATE
  end

  # =========================================================================
  # DELAY EFFECT
  # =========================================================================
  # Simple echo: delayed copy of signal mixed with original

  def apply_delay(samples, delay_time: 0.5, feedback: 0.4, wet_mix: 0.5)
    # delay_time: seconds before echo repeats
    # feedback: how much of delay feeds back (0-1, typically 0.3-0.5)
    # wet_mix: balance between dry (0) and wet (1) signal

    return samples if delay_time <= 0

    delay_samples = (delay_time * @sample_rate).to_i
    return samples if delay_samples >= samples.size

    output = Array.new(samples.size, 0.0)
    delayed = Array.new(samples.size + delay_samples, 0.0)

    # Write input to delayed buffer
    samples.each_with_index do |sample, i|
      delayed[i] = sample.to_f / MAX_AMPLITUDE
    end

    # Process with feedback
    (0...samples.size).each do |i|
      # Current sample + feedback from delayed version
      delayed[i + delay_samples] += delayed[i] * feedback
    end

    # Mix dry and wet signals
    (0...samples.size).each do |i|
      dry = samples[i].to_f / MAX_AMPLITUDE
      wet = delayed[i + delay_samples]
      output[i] = (dry * (1.0 - wet_mix)) + (wet * wet_mix)
    end

    normalize_float(output)
  end

  # =========================================================================
  # REVERB EFFECT
  # =========================================================================
  # Simple reverb using comb filters (Freeverb-style)

  def apply_reverb(samples, room_size: 0.5, damping: 0.5, wet_mix: 0.4)
    # room_size: (0-1) size of virtual room
    # damping: (0-1) high frequency damping
    # wet_mix: balance between dry and wet

    return samples if wet_mix <= 0

    # Comb filter delays (in samples) - prime numbers for better diffusion
    comb_delays = [1116, 1188, 1277, 1356]  # ~25ms at 44.1kHz

    output = Array.new(samples.size, 0.0)
    normalized_input = samples.map { |s| s.to_f / MAX_AMPLITUDE }

    # Initialize comb filter buffers
    comb_buffers = comb_delays.map { |delay| Array.new(delay, 0.0) }
    comb_filter_stores = Array.new(comb_delays.size, 0.0)
    comb_indices = Array.new(comb_delays.size, 0)

    # Process each sample through all comb filters
    (0...samples.size).each do |i|
      input = normalized_input[i]
      comb_output = 0.0

      comb_delays.each_with_index do |delay, j|
        buffer = comb_buffers[j]
        idx = comb_indices[j]

        # Read from buffer
        buffered = buffer[idx]

        # Damping filter
        filter_store = comb_filter_stores[j]
        output_val = buffered * (1.0 - damping) + filter_store * damping
        comb_filter_stores[j] = output_val

        # Write to buffer with feedback
        buffer[idx] = input + (output_val * room_size)

        # Move to next sample in circular buffer
        comb_indices[j] = (idx + 1) % delay

        comb_output += output_val
      end

      # Mix dry and wet with gain reduction on reverb
      dry = normalized_input[i]
      # Divide comb output by number of filters and reduce by additional factor
      wet = comb_output / comb_delays.size.to_f * 0.85
      output[i] = (dry * (1.0 - wet_mix)) + (wet * wet_mix)
    end

    normalize_float(output)
  end

  # =========================================================================
  # TREMOLO EFFECT
  # =========================================================================
  # Amplitude modulation - volume wobbles at modulation frequency

  def apply_tremolo(samples, rate: 5.0, depth: 0.5)
    # rate: modulation frequency (Hz), typically 2-10 Hz
    # depth: modulation depth (0-1), 1.0 = full silence at minimum

    return samples if depth <= 0

    output = samples.map do |sample|
      sample.to_f
    end

    (0...samples.size).each do |i|
      t = i.to_f / @sample_rate
      # LFO (Low Frequency Oscillator) - sine wave modulation
      lfo = Math.sin(2 * Math::PI * rate * t)
      # Map LFO from [-1, 1] to [1-depth, 1]
      modulation = 1.0 - (depth * (1.0 - lfo) / 2.0)
      output[i] *= modulation
    end

    output.map { |s| s.to_i }
  end

  # =========================================================================
  # VIBRATO EFFECT
  # =========================================================================
  # Frequency modulation - pitch wobbles

  def apply_vibrato(samples, rate: 5.0, depth: 10.0)
    # rate: LFO frequency (Hz), typically 2-10 Hz
    # depth: pitch variation in semitones (typically 1-3)
    # Note: This is a time-domain approximation using sample delay modulation

    return samples if depth <= 0

    max_delay_samples = (depth * @sample_rate / 1200.0).to_i + 1  # depth in ms roughly
    return samples if max_delay_samples > samples.size / 2

    output = Array.new(samples.size, 0.0)
    buffer = samples.map { |s| s.to_f / MAX_AMPLITUDE }

    (0...samples.size).each do |i|
      t = i.to_f / @sample_rate
      # LFO modulates delay time
      lfo = Math.sin(2 * Math::PI * rate * t)
      delay_amount = max_delay_samples * (lfo + 1.0) / 2.0

      # Linear interpolation for fractional sample delay
      delay_int = delay_amount.to_i
      delay_frac = delay_amount - delay_int

      if i >= delay_int + 1
        sample_a = buffer[i - delay_int]
        sample_b = buffer[i - delay_int - 1]
        output[i] = sample_a * (1.0 - delay_frac) + sample_b * delay_frac
      elsif i >= delay_int
        output[i] = buffer[i - delay_int]
      else
        output[i] = buffer[i]
      end
    end

    normalize_float(output)
  end

  # =========================================================================
  # CHORUS EFFECT
  # =========================================================================
  # Slight delay with modulation - creates thickening effect

  def apply_chorus(samples, delay_time: 0.02, rate: 1.5, depth: 0.002)
    # delay_time: base delay in seconds (typically 10-50ms)
    # rate: LFO rate in Hz (typically 0.5-2 Hz for subtle effect)
    # depth: amount of delay modulation in seconds

    return samples if delay_time <= 0

    base_delay_samples = (delay_time * @sample_rate).to_i
    max_depth_samples = (depth * @sample_rate).to_i

    output = Array.new(samples.size, 0.0)
    buffer = samples.map { |s| s.to_f / MAX_AMPLITUDE }

    # Create delay buffer
    delay_buffer = Array.new(base_delay_samples + max_depth_samples + 1, 0.0)
    write_index = 0

    (0...samples.size).each do |i|
      t = i.to_f / @sample_rate

      # Modulate delay
      lfo = Math.sin(2 * Math::PI * rate * t)
      delay_samples = base_delay_samples + (max_depth_samples * (lfo + 1.0) / 2.0)

      # Write to circular buffer
      delay_buffer[write_index] = buffer[i]
      write_index = (write_index + 1) % delay_buffer.size

      # Read from modulated position
      read_index = (write_index - delay_samples.to_i) % delay_buffer.size
      read_index = read_index < 0 ? read_index + delay_buffer.size : read_index

      # Mix original and delayed
      output[i] = (buffer[i] * 0.7) + (delay_buffer[read_index] * 0.3)
    end

    normalize_float(output)
  end

  # =========================================================================
  # EFFECT CHAIN
  # =========================================================================
  # Apply multiple effects in sequence

  def apply_effects(samples, effects_chain)
    # effects_chain: array of hashes with :effect and :params
    # Example: [{effect: :delay, params: {delay_time: 0.5}}, ...]

    result = samples

    effects_chain.each do |effect_spec|
      effect_name = effect_spec[:effect]
      params = effect_spec[:params] || {}

      case effect_name
      when :delay
        result = apply_delay(result, **params)
      when :reverb
        result = apply_reverb(result, **params)
      when :tremolo
        result = apply_tremolo(result, **params)
      when :vibrato
        result = apply_vibrato(result, **params)
      when :chorus
        result = apply_chorus(result, **params)
      end
    end

    result
  end

  # =========================================================================
  # UTILITIES
  # =========================================================================

  private

  def normalize_float(samples)
    # Normalize float samples to PCM range with headroom to prevent clipping
    peak = samples.map(&:abs).max || 1.0
    peak = 1.0 if peak < 0.001

    # Apply headroom reduction (0.9 instead of 1.0) to prevent clipping
    # and provide margin for multiple effects in chain
    headroom = 0.9
    normalized = samples.map { |s| s / peak * headroom }

    # Convert to PCM with clipping safety net
    normalized.map do |s|
      pcm_value = (s * MAX_AMPLITUDE).to_i
      # Hard limit to prevent any overflow
      [[pcm_value, MAX_AMPLITUDE].min, -MAX_AMPLITUDE].max
    end
  end
end
