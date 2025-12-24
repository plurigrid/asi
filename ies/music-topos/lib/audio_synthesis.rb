# lib/audio_synthesis.rb
require 'socket'

class AudioSynthesis
  SAMPLE_RATE = 44100
  BIT_DEPTH = 16
  MAX_AMPLITUDE = 32767 # 2^15 - 1

  def initialize(output_file: '/tmp/audio.wav')
    @output_file = output_file
  end

  def render_score(score_events, tempo: 120)
    return @output_file if score_events.empty?

    seconds_per_beat = 60.0 / tempo

    timed_events = score_events.map do |event|
      start_sec = event[:at] * seconds_per_beat
      dur_sec = event[:dur] * seconds_per_beat
      audio = event[:audio] || {}
      {
        start_sample: (start_sec * SAMPLE_RATE).to_i,
        duration: dur_sec,
        frequencies: audio[:frequencies] || [440],
        amplitude: audio[:amplitude] || 0.5
      }
    end

    total_samples = timed_events.map { |e| e[:start_sample] + (e[:duration] * SAMPLE_RATE).to_i }.max
    mixed = Array.new(total_samples, 0.0)

    timed_events.each do |event|
      samples = generate_mixed_wave_float(event[:frequencies], event[:duration], event[:amplitude])
      samples.each_with_index do |s, i|
        idx = event[:start_sample] + i
        mixed[idx] += s if idx < total_samples
      end
    end

    peak = mixed.map(&:abs).max
    if peak > 1.0
      mixed = mixed.map { |s| s / peak }
    end

    pcm = mixed.map { |s| (s * MAX_AMPLITUDE).to_i }
    write_wav_file(pcm, @output_file)
    @output_file
  end

  def render_sequence(sequence, silence_between: 0.1)
    full_samples = []
    
    sequence.each do |event|
      freqs = event[:frequencies]
      freqs = [freqs] unless freqs.is_a?(Array)
      duration = event[:duration] || 1.0
      amplitude = event[:amplitude] || 0.5
      
      event_samples = generate_mixed_wave(freqs, duration, amplitude)
      full_samples.concat(event_samples)
      
      if silence_between > 0
        silence_samples = Array.new((silence_between * SAMPLE_RATE).to_i, 0)
        full_samples.concat(silence_samples)
      end
    end
    
    write_wav_file(full_samples, @output_file)
    @output_file
  end

  def generate_sine_wave(frequency, duration, amplitude)
    samples_count = (duration * SAMPLE_RATE).to_i
    (0...samples_count).map do |i|
      t = i.to_f / SAMPLE_RATE
      sample = amplitude * Math.sin(2 * Math::PI * frequency * t)
      (sample * MAX_AMPLITUDE).to_i
    end
  end

  def generate_mixed_wave_float(frequencies, duration, amplitude)
    samples_count = (duration * SAMPLE_RATE).to_i
    mixed = Array.new(samples_count, 0.0)
    
    frequencies.each do |freq|
      (0...samples_count).each do |i|
        t = i.to_f / SAMPLE_RATE
        voice_amp = amplitude / frequencies.size.to_f
        mixed[i] += voice_amp * Math.sin(2 * Math::PI * freq * t)
      end
    end
    
    mixed
  end

  def generate_mixed_wave(frequencies, duration, amplitude)
    generate_mixed_wave_float(frequencies, duration, amplitude).map { |s| (s * MAX_AMPLITUDE).to_i }
  end

  def write_wav_file(samples, filename)
    file = File.open(filename, 'wb')
    
    # WAV Header
    # ChunkID "RIFF"
    file.write('RIFF')
    # ChunkSize (36 + SubChunk2Size)
    data_size = samples.size * 2 # 2 bytes per sample (16-bit)
    file.write([36 + data_size].pack('V')) 
    # Format "WAVE"
    file.write('WAVE')
    
    # Subchunk1 "fmt "
    file.write('fmt ')
    # Subchunk1Size (16 for PCM)
    file.write([16].pack('V'))
    # AudioFormat (1 for PCM)
    file.write([1].pack('v'))
    # NumChannels (1 for Mono for simplicity, or we duplicate for stereo)
    # Let's use Mono as default based on generation code above
    channels = 1 
    file.write([channels].pack('v'))
    # SampleRate
    file.write([SAMPLE_RATE].pack('V'))
    # ByteRate (SampleRate * NumChannels * BitsPerSample/8)
    file.write([SAMPLE_RATE * channels * BIT_DEPTH / 8].pack('V'))
    # BlockAlign (NumChannels * BitsPerSample/8)
    file.write([channels * BIT_DEPTH / 8].pack('v'))
    # BitsPerSample
    file.write([BIT_DEPTH].pack('v'))
    
    # Subchunk2 "data"
    file.write('data')
    # Subchunk2Size
    file.write([data_size].pack('V'))
    
    # Data
    # Convert samples to binary
    # Clamp to 16-bit range first to be safe
    packed_data = samples.map do |s| 
      val = [[s, -32768].max, 32767].min
      val
    end.pack('v*') # 'v' is 16-bit little-endian
    
    file.write(packed_data)
    file.close
  end
end
