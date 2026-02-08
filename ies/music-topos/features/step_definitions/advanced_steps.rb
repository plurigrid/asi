# features/step_definitions/advanced_steps.rb

require 'rspec'
require_relative '../../lib/spectral'
require_relative '../../lib/worlds/spectral_world'

Given('a fundamental frequency of {float} Hz \(C3)') do |freq|
  @fundamental = freq
end

When('I generate {int} partials') do |n|
  @spectrum = Spectrum.new(@fundamental, n)
end

Then('the frequencies are integer multiples of the fundamental') do
  @spectrum.partials.each_with_index do |f, i|
    expect(f).to be_within(0.01).of(@fundamental * (i + 1))
  end
end

Then('the MIDI notes correspond to the natural overtone series') do
  midi = @spectrum.in_midi
  expect(midi[0]).to be_within(0.1).of(48.0) # C3
  expect(midi[1]).to be_within(0.1).of(60.0) # C4
  expect(midi[2]).to be_within(0.1).of(67.0) # G4 (approx)
end
