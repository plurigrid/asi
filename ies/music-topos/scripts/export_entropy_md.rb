#!/usr/bin/env ruby
# scripts/export_entropy_md.rb
#
# Export interaction entropy as GitHub-compatible markdown with Mermaid diagrams

$LOAD_PATH.unshift File.expand_path('../lib', __dir__)

require 'interaction_entropy'
require 'json'

manager = InteractionEntropy.new_manager(seed: 0x42D)
triad = InteractionEntropy.skill_triad(
  generator: 'rubato-composer',
  coordinator: 'glass-bead-game', 
  validator: 'bisimulation-game',
  manager: manager
)

9.times { |i| triad[[:generator, :coordinator, :validator][i % 3]].invoke("I#{i+1}") }

puts '# Interaction Entropy Report'
puts ''
puts '## Mermaid Diagram'
puts ''
puts '```mermaid'
puts 'flowchart LR'
manager.interactions.each_with_index do |i, idx|
  color = i.trit == 1 ? '#D82626' : (i.trit == -1 ? '#2626D8' : '#26D826')
  puts "    I#{idx}[\"#{i.skill_name}\nH=#{i.color[:H].round(0)}°\"]"
  puts "    style I#{idx} fill:#{color}"
end
puts '```'
puts ''
puts '## GF(3) Triplets'
puts ''
manager.triplets.each_with_index do |t, i|
  status = t[:gf3_conserved] ? '✓' : '✗'
  puts "#{i + 1}. trits=[#{t[:trits].join(', ')}] sum=#{t[:trit_sum]} #{status}"
end
puts ''
puts '## Statistics'
puts ''
puts '```json'
puts JSON.pretty_generate(manager.summary)
puts '```'
