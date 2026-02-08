# features/step_definitions/polyphony_steps.rb

require 'rspec'
require_relative '../../lib/pitch_class'
require_relative '../../lib/chord'
require_relative '../../lib/voice_leading'
require_relative '../../lib/worlds/polyphonic_world'

Given('a C Major chord in SATB voicing: [E4, C4, G3, C3]') do
  @chord1 = Chord.from_notes(['E', 'C', 'G', 'C'])
  @octaves1 = [4, 4, 3, 3]
end

When('I transition to an F Major chord with minimal motion') do
  @chord2 = Chord.from_notes(['F', 'C', 'A', 'F'])
  @octaves2 = [4, 4, 3, 3]
  @analysis = VoiceLeading.smoothness_analysis(@chord1, @octaves1, @chord2, @octaves2)
end

Then('the Soprano moves from E4 to F4 \({int} semitone)') do |dist|
  midi1 = @chord1.voices[0].to_midi(@octaves1[0])
  midi2 = @chord2.voices[0].to_midi(@octaves2[0])
  expect((midi2 - midi1).abs).to eq(dist)
end

Then('the Alto moves from C4 to C4 \({int} semitones)') do |dist|
  midi1 = @chord1.voices[1].to_midi(@octaves1[1])
  midi2 = @chord2.voices[1].to_midi(@octaves2[1])
  expect((midi2 - midi1).abs).to eq(dist)
end

Then('the Tenor moves from G3 to A3 \({int} semitones)') do |dist|
  midi1 = @chord1.voices[2].to_midi(@octaves1[2])
  midi2 = @chord2.voices[2].to_midi(@octaves2[2])
  expect((midi2 - midi1).abs).to eq(dist)
end

Then('the Bass moves from C3 to F3 \({int} semitones)') do |dist|
  midi1 = @chord1.voices[3].to_midi(@octaves1[3])
  midi2 = @chord2.voices[3].to_midi(@octaves2[3])
  expect((midi2 - midi1).abs).to eq(dist)
end

Then('the total voice leading distance is {int} semitones') do |dist|
  expect(@analysis[:total_motion]).to eq(dist)
end
