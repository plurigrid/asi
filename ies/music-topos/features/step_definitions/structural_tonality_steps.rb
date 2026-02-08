# features/step_definitions/structural_tonality_steps.rb

require 'rspec'
require_relative '../../lib/pitch_class'
require_relative '../../lib/chord'
require_relative '../../lib/structure'

Given('a progression [G Major, C Major] in C Major') do
  @chords = [Chord.from_notes(['G', 'B', 'D']), Chord.from_notes(['C', 'E', 'G'])]
  @key = 'C'
end

When('I analyze the cadence type') do
  @cadence = Cadence.detect(@chords, @key)
end

Then('it is identified as an {string}') do |type|
  expect(@cadence.to_s.gsub('_', ' ')).to eq(type.downcase)
end

Then('it achieves structural closure') do
  expect([:authentic, :plagal]).to include(@cadence)
end

Given('a progression [V, vi]') do
  # V to vi in C Major
  @chords = [Chord.from_notes(['G', 'B', 'D']), Chord.from_notes(['A', 'C', 'E'])]
  @key = 'C'
end

When('I analyze the tonal resolution') do
  @cadence = Cadence.detect(@chords, @key)
end

Then('the appearance intensity reflects the subversion of expectation') do
  # This matches the Badiouian intensity concept
  expect(@cadence).to eq(:deceptive)
end
