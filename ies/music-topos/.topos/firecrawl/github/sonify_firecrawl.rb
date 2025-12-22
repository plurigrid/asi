#!/usr/bin/env ruby

require 'json'
require 'zlib'
require_relative '../../../lib/audio_synthesis'

INDEX_PATH = File.expand_path('index.json', __dir__)
OUT_WAV = File.expand_path('../firecrawl_sonification.wav', __dir__)
OUT_JSON = File.expand_path('../firecrawl_sonification.json', __dir__)

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
# Generates a simple major triad per item.

def base_frequency(url)
  hash = Zlib.crc32(url)
  110.0 + (hash % 48) * 5.0
end

def triad(base)
  [base, base * 5.0 / 4.0, base * 3.0 / 2.0]
end

sequence = []
items.each_with_index do |item, idx|
  url = item['url'].to_s
  base = base_frequency(url)
  chord = triad(base)
  topics_count = (item['topics'] || []).size
  duration = [0.35 + topics_count * 0.08, 1.6].min
  amplitude = item['status'] == 'not_found' ? 0.22 : 0.42
  label = "#{idx + 1}: #{item['repo'] || url}"

  sequence << {
    frequencies: chord,
    duration: duration,
    amplitude: amplitude,
    label: label
  }
end

puts "Rendering #{sequence.size} events to #{OUT_WAV}"

synth = AudioSynthesis.new(output_file: OUT_WAV)
output = synth.render_sequence(sequence, silence_between: 0.12)

File.write(OUT_JSON, JSON.pretty_generate({
  generated_at: Time.now.utc.strftime('%Y-%m-%dT%H:%M:%SZ'),
  source_index: INDEX_PATH,
  output_wav: OUT_WAV,
  event_count: sequence.size,
  events: sequence
}))

puts "Wrote: #{output}"
puts "Wrote: #{OUT_JSON}"
