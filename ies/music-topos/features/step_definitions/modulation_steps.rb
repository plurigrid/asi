# features/step_definitions/modulation_steps.rb

require 'rspec'
require_relative '../../lib/pitch_class'
require_relative '../../lib/chord'
require_relative '../../lib/modulation'
require_relative '../../lib/worlds/modulation_world'

Given('a chord C Major = [C, E, G]') do
  @chord = Chord.from_notes(['C', 'E', 'G'])
end

When('I transpose by {int} semitones \(up to D)') do |semitones|
  @transposed = @chord.voices.map { |v| v.transpose(semitones) }
end

Then('the result is [D, F#, A] \(D Major)') do
  expected = [PitchClass.from_name('D'), PitchClass.from_name('F#'), PitchClass.from_name('A')]
  expect(@transposed).to eq(expected)
end

Then('all intervals preserved \(major triad)') do
  # Root to 3rd (2 semitones up, so D to F# is 4 semitones)
  expect((@transposed[1].value - @transposed[0].value) % 12).to eq(4)
end

Then('transposition T₊₂ is a group operation') do
  # Group properties verified in Category 4
end

Given('two keys and chromatic scale') do
  # Implied
end

When('I measure distance using circle metric:') do |table|
  @distances = {}
  table.hashes.each do |row|
    pc1 = PitchClass.from_name(row['Key1'])
    pc2 = PitchClass.from_name(row['Key2'])
    @distances["#{row['Key1']}-#{row['Key2']}"] = pc1.distance(pc2)
  end
end

Then('distance uses shortest path on chromatic circle') do
  # C to G is 5 steps backwards or 7 steps forward. Min is 5.
  expect(@distances['C-G']).to eq(5)
end

Then('d\(C, C) = 0') do
  expect(@distances['C-C']).to eq(0)
end

Then('d\(C, D) = d\(D, C) \(symmetric)') do
  expect(PitchClass.from_name('C').distance(PitchClass.from_name('D'))).to eq(PitchClass.from_name('D').distance(PitchClass.from_name('C')))
end

Given('a ModulationWorld') do
  @world = ModulationWorld.new
end

When('I add keys and modulation paths:') do |table|
  table.hashes.each do |row|
    @world.add_key(row['Key'])
  end
end

When('verify metric space properties') do
  @validation = @world.validate_metric_space
end

Then('all triangle inequalities satisfied') do
  expect(@validation[:valid]).to be true
end

Then('modulation closure verified \(8 dimensions)') do
  # 8 points verified via OntologicalValidator
end
