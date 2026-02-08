# features/step_definitions/progression_steps.rb

require 'rspec'
require_relative '../../lib/pitch_class'
require_relative '../../lib/chord'
require_relative '../../lib/progressions'

Given('a progression [I, IV, V, I] in C Major') do
  @chords = [
    Chord.from_notes(['C', 'E', 'G']),
    Chord.from_notes(['F', 'A', 'C']),
    Chord.from_notes(['G', 'B', 'D']),
    Chord.from_notes(['C', 'E', 'G'])
  ]
  @key = 'C'
end

When('I analyze the harmonic functions') do
  @analysis = HarmonicProgression.analyze(@chords, @key)
end

Then('the sequence is [Tonic, Subdominant, Dominant, Tonic]') do
  expect(@analysis).to eq([:tonic, :subdominant, :dominant, :tonic])
end

Then('the progression is marked as functionally closed') do
  closure = HarmonicFunction.functional_closure(@chords)
  expect(closure[:complete]).to be true
end

Given('a chord [G, B, D] in the key of C Major') do
  @chord = Chord.from_notes(['G', 'B', 'D'])
  @key = 'C'
end

When('I perform Roman numeral analysis') do
  @roman = HarmonicProgression.roman_numeral(@chord, @key)
end

Then('the result is {string}') do |numeral|
  expect(@roman).to eq(numeral)
end

Then('its function is identified as Dominant') do
  expect(HarmonicFunction.analyze_function(@chord.root, @key)).to eq(:dominant)
end
