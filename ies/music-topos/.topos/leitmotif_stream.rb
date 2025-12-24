#!/usr/bin/env ruby
# bin/leitmotif_stream.rb
#
# LEITMOTIF STREAMING: Real-time audio output without WAV files
# Generates WAV headers on-the-fly and streams directly to afplay

puts "=" * 80
puts "🎵 LEITMOTIF EVOLUTION: Real-Time Direct Streaming"
puts "=" * 80
puts ""

# Stream WAV audio using named pipe (FIFO) - no intermediate disk files
def stream_leitmotif_audio(transformations = [])
  require 'tmpdir'
  require 'fileutils'

  sample_rate = 44100
  total_samples = transformations.sum { |t| (sample_rate * t[:duration]).to_i }

  # Create temporary named pipe (FIFO)
  fifo_path = File.join(Dir.tmpdir, "leitmotif_#{Process.pid}.fifo")

  begin
    # Create FIFO
    system("mkfifo #{fifo_path}")

    # Start afplay in background reading from FIFO
    afplay_thread = Thread.new do
      system("afplay #{fifo_path}")
    end

    # Give afplay time to open the FIFO
    sleep 0.2

    # Write WAV header and data to FIFO
    File.open(fifo_path, 'wb') do |f|
      byte_rate = sample_rate * 2
      subchunk2_size = total_samples * 2
      chunk_size = 36 + subchunk2_size

      # Write WAV header
      f.write('RIFF')
      f.write([chunk_size].pack('V'))
      f.write('WAVE')
      f.write('fmt ')
      f.write([16].pack('V'))
      f.write([1].pack('v'))       # PCM
      f.write([1].pack('v'))       # mono
      f.write([sample_rate].pack('V'))
      f.write([byte_rate].pack('V'))
      f.write([2].pack('v'))
      f.write([16].pack('v'))
      f.write('data')
      f.write([subchunk2_size].pack('V'))

      # Generate and stream each transformation
      transformations.each do |transform|
        chord_samples = (sample_rate * transform[:duration]).to_i
        puts "▶️  #{transform[:name]} (#{transform[:duration]}s)..."
        $stdout.flush

        chord_samples.times do |i|
          sample = 0.0
          transform[:frequencies].each do |freq|
            sample += Math.sin(2 * Math::PI * freq * i / sample_rate) * 0.25
          end

          # Convert to 16-bit signed integer and stream
          pcm_value = (sample * 32767).to_i
          f.write([pcm_value].pack('s<'))
        end
      end
    end

    # Wait for afplay to finish
    afplay_thread.join
  ensure
    # Clean up FIFO
    File.delete(fifo_path) if File.exist?(fifo_path)
  end
end

# THE CORE LEITMOTIF: C Major chord
core_leitmotif = [262, 330, 392]  # C-E-G (TONIC)

puts "LEITMOTIF TRANSFORMATIONS:"
puts "━" * 80
puts ""

puts "1️⃣  TONIC (T): Home State"
puts "   Frequencies: #{core_leitmotif.join(', ')} Hz (C Major triad)"
puts ""

subdominant = [349, 440, 523]  # F-A-C
puts "2️⃣  SUBDOMINANT (S): Preparation"
puts "   Frequencies: #{subdominant.join(', ')} Hz (F Major triad)"
puts ""

dominant = [392, 494, 587]  # G-B-D
puts "3️⃣  DOMINANT (D): Maximum Tension"
puts "   Frequencies: #{dominant.join(', ')} Hz (G Major triad)"
puts ""

puts "4️⃣  RETURN TO TONIC (T): Resolution"
puts "   Frequencies: #{core_leitmotif.join(', ')} Hz (C Major triad)"
puts ""

puts "=" * 80
puts "STREAMING AUDIO..."
puts "=" * 80
puts ""

transformations = [
  { frequencies: core_leitmotif,     name: "TONIC (T)",       duration: 2.0 },
  { frequencies: subdominant,        name: "SUBDOMINANT (S)", duration: 2.0 },
  { frequencies: dominant,           name: "DOMINANT (D)",    duration: 2.0 },
  { frequencies: core_leitmotif,     name: "RETURN TO T",     duration: 3.0 }
]

start_time = Time.now
stream_leitmotif_audio(transformations)
elapsed = Time.now - start_time

puts ""
puts "=" * 80
puts "✅ STREAMING COMPLETE"
puts "=" * 80
puts ""
puts "Streaming performance:"
puts "  • Total time: #{elapsed.round(3)}s"
puts "  • Real-time ratio: #{(9.0 / elapsed).round(2)}x (positive = faster than real-time)"
puts "  • Direct to system audio, no intermediate files"
puts ""
