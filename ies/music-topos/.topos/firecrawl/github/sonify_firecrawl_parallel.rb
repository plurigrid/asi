#!/usr/bin/env ruby

require 'json'
require 'zlib'
require_relative '../../../lib/audio_synthesis'

INDEX_PATH = File.expand_path('index.json', __dir__)
OUT_WAV = File.expand_path('../firecrawl_sonification_parallel.wav', __dir__)
OUT_JSON = File.expand_path('../firecrawl_sonification_parallel.json', __dir__)

unless File.exist?(INDEX_PATH)
  warn "Missing index: #{INDEX_PATH}"
  exit 1
end

index = JSON.parse(File.read(INDEX_PATH))
items = (index['items'] || []).sort_by { |item| item['url'].to_s }

if items.empty?
  warn 'No items found in index.json'
  exit 1
end

# Deterministic mapping: URL -> CRC32 -> base frequency.
# Parallelize by splitting items into independent streams and overlapping them.

def base_frequency(url, stream_idx)
  hash = Zlib.crc32(url)
  base = 90.0 + (hash % 60) * 4.0
  base * (1.0 + (stream_idx * 0.03))
end

def triad(base)
  [base, base * 5.0 / 4.0, base * 3.0 / 2.0]
end

stream_count = 4
streams = Array.new(stream_count) { [] }
items.each_with_index { |item, idx| streams[idx % stream_count] << item }

score_events = []
streams.each_with_index do |stream, s_idx|
  t = 0.0
  stream.each_with_index do |item, i_idx|
    url = item['url'].to_s
    base = base_frequency(url, s_idx)
    chord = triad(base)
    topics_count = (item['topics'] || []).size
    duration = [0.4 + topics_count * 0.06, 1.4].min
    amplitude = item['status'] == 'not_found' ? 0.18 : 0.28

    score_events << {
      at: t,
      dur: duration,
      audio: {
        frequencies: chord,
        amplitude: amplitude
      },
      label: "S#{s_idx + 1}-#{i_idx + 1}: #{item['repo'] || url}"
    }

    # Slightly stagger within stream for motion.
    t += duration * 0.75
  end
end

puts "Rendering parallel score with #{score_events.size} events to #{OUT_WAV}"

synth = AudioSynthesis.new(output_file: OUT_WAV)
# tempo 60 => beats are seconds, so at/dur are seconds
output = synth.render_score(score_events, tempo: 60)

File.write(OUT_JSON, JSON.pretty_generate({
  generated_at: Time.now.utc.strftime('%Y-%m-%dT%H:%M:%SZ'),
  source_index: INDEX_PATH,
  output_wav: OUT_WAV,
  stream_count: stream_count,
  event_count: score_events.size,
  events: score_events
}))

puts "Wrote: #{output}"
puts "Wrote: #{OUT_JSON}"
