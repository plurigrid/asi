# features/step_definitions/pitch_space_steps.rb

require 'rspec'
require_relative '../../lib/pitch_class'
require_relative '../../lib/semantic_closure_validator'

# ELICITATION: What is a pitch class?
# The test will guide us to build a PitchClass that understands the circle group

Given('a MIDI note {int} with name {word}') do |midi_note, note_name|
  @midi_note = midi_note
  @note_name = note_name
end

When('I create a pitch class from this MIDI note') do
  @pitch_class = PitchClass.from_midi(@midi_note)
end

Then('the pitch class should be {int} with name {word} modulo {int}') do |expected, pc_name, mod|
  expect(@pitch_class.value).to eq(expected)
  expect(@pitch_class.value).to be_between(0, mod - 1)
end

# ELICITATION: Can we transpose in the circle group?
# The test demands that PitchClass understand group structure

Given(/^pitch class (\d+) \((\w+)\)$/) do |pc_value, pc_name|
  @pitch_class = PitchClass.new(pc_value.to_i)
end

When(/^I transpose by (\d+) semitones$/) do |semitones|
  @transposed = @pitch_class.transpose(semitones.to_i)
end

Then(/^I get pitch class (\d+) \((\w+)\)$/) do |expected, pc_name|
  expect(@transposed.value).to eq(expected.to_i)
end

Then('transposing {int} by {int} should equal transposing {int} by {int}') do |pc1, trans1, pc2, trans2|
  pc1_transposed = PitchClass.new(pc1).transpose(trans1)
  pc2_transposed = PitchClass.new(pc2).transpose(trans2)
  expect(pc1_transposed.value).to eq(pc2_transposed.value)
end

# ELICITATION: Is this a line or a circle?
# The metric test demands topological correctness

Given(/^pitch class (\d+) \((\w+)\)$/) do |pc_value, pc_name|
  @pitch_class1 = PitchClass.new(pc_value.to_i)
end

Given(/^pitch class (\d+) \((\w+)\) as second$/) do |pc_value, pc_name|
  @pitch_class2 = PitchClass.new(pc_value.to_i)
end

# Note: Cucumber step consolidation
And(/^pitch class (\d+) \((\w+)\)$/) do |pc_value, pc_name|
  @pitch_class2 = PitchClass.new(pc_value.to_i)
end

When('I compute distance on the pitch circle') do
  @distance = @pitch_class1.distance(@pitch_class2)
end

Then(/^the distance should be (\d+) \(not (\d+)\)$/) do |expected, not_expected|
  expect(@distance).to eq(expected.to_i)
  expect(@distance).not_to eq(not_expected.to_i)
end

# ELICITATION: Can the system validate its own completeness?
# The semantic closure test demands self-validation

Given('a composition with notes {string}') do |notes_str|
  # Parse [0, 4, 7] into array
  notes_array = eval(notes_str)
  @composition = {
    notes: notes_array.map { |n| PitchClass.new(n) }
  }
end

When('I validate semantic closure for pitch space') do
  @validation = SemanticClosureValidator.validate_pitch_space(@composition)
end

Then('all notes should be valid pitch classes in Z¹²') do
  @composition[:notes].each do |pc|
    expect(pc.value).to be_between(0, 11)
  end
end

Then('the system should report pitch_space closure: VALID') do
  expect(@validation[:valid]).to be true
  expect(@validation[:report][:pitch_space]).to eq(:VALID)
end
