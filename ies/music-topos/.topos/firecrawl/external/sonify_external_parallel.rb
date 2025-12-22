#!/usr/bin/env ruby

require 'json'
require 'uri'
require 'zlib'
require_relative '../../../lib/audio_synthesis'

INDEX_PATH = File.expand_path('index.json', __dir__)
OUT_WAV = File.expand_path('external_sonification_parallel.wav', __dir__)
OUT_JSON = File.expand_path('external_sonification_parallel.json', __dir__)

unless File.exist?(INDEX_PATH)
  warn "Missing index: #{INDEX_PATH}"
  exit 1
end

index = JSON.parse(File.read(INDEX_PATH))
items = (index['items'] || []).select { |i| i['url'] }
if items.empty?
  warn 'No items found in index.json'
  exit 1
end

stream_count = 6
streams = Array.new(stream_count) { [] }

def base_frequency(url, stream_idx)
  hash = Zlib.crc32(url)
  base = 80.0 + (hash % 72) * 3.5
  base * (1.0 + (stream_idx * 0.025))
end

def triad(base)
  [base, base * 5.0 / 4.0, base * 3.0 / 2.0]
end

items.each do |item|
  begin
    host = URI.parse(item['url']).host.to_s
  rescue StandardError
    host = item['url'].to_s
  end
  bucket = (Zlib.crc32(host) % stream_count)
  streams[bucket] << item
end

score_events = []
streams.each_with_index do |stream, s_idx|
  t = 0.0
  stream.sort_by { |i| i['url'].to_s }.each do |item|
    url = item['url'].to_s
    base = base_frequency(url, s_idx)
    chord = triad(base)
    topics_count = (item['topics'] || []).size
    duration = [0.35 + topics_count * 0.07, 1.5].min
    amplitude = item['status'] == 'ok' ? 0.26 : 0.16

    score_events << {
      at: t,
      dur: duration,
      audio: {
        frequencies: chord,
        amplitude: amplitude
      },
      label: "S#{s_idx + 1}: #{item['url']}"
    }

    t += duration * 0.7
  end
end

puts "Rendering parallel external score with #{score_events.size} events to #{OUT_WAV}"

synth = AudioSynthesis.new(output_file: OUT_WAV)
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
