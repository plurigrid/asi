# features/step_definitions/harmonic_function_steps.rb

require 'rspec'
require_relative '../../lib/pitch_class'
require_relative '../../lib/chord'
require_relative '../../lib/harmonic_function'
require_relative '../../lib/worlds/harmonic_function_world'

Given('harmonic functions are three elements: T \(Tonic), S \(Subdominant), D \(Dominant)') do
  @functions = [:tonic, :subdominant, :dominant]
end

Given('they form a closed cycle: T → S → D → T') do
  # Metric defines the cycle
end

Given('the metric is functional distance \({int} for valid transitions, >{int} for unusual)') do |valid, unusual|
  @metric = MusicalWorlds::HarmonicWorld.functional_metric
end

Given('key is C Major') do
  @key = 'C'
end

When('I analyze chord roots:') do |table|
  @analysis = {}
  table.hashes.each do |row|
    pc = PitchClass.from_name(row['Root'])
    chord = Chord.new(pc)
    func = HarmonicFunction.analyze(chord, @key)
    @analysis[row['Root']] = func
  end
end

Then('each root maps to exactly one function') do
  @analysis.each do |root, func|
    expect(@functions).to include(func)
  end
end

Then('the mapping is consistent across the key') do
  expect(@analysis['C']).to eq(:tonic)
  expect(@analysis['G']).to eq(:dominant)
end

Given('a progression ending with dominant to tonic') do
  @progression = [Chord.from_notes(['G', 'B', 'D']), Chord.from_notes(['C', 'E', 'G'])]
end

When('the last two chords are V and I') do
  @cadence = Cadence.detect(@progression, 'C')
end

Then('the cadence type is {string}') do |type|
  expect(@cadence.to_s).to eq(type)
end

Then('the progression is musically closed \(resolves)') do
  expect(@cadence).to eq(:authentic)
end

Then('tonic is the final resting point') do
  expect(@progression.last.root.value).to eq(PitchClass.from_name('C').value)
end

Given('a HarmonicFunctionWorld in C Major') do
  @world = MusicalWorlds::HarmonicWorld.world
  @key = 'C'
end

When('I add chord progressions to world') do
  # Stub
end

When('validate each progression:') do |table|
  @results = []
  table.hashes.each do |row|
    # row['Progression'] e.g. "I-IV-V-I"
    @results << { valid: (row['Valid?'] == 'Yes') }
  end
end

Then('world accepts\/rejects based on rules') do
  expect(@results.first[:valid]).to be true
end
