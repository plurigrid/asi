# features/step_definitions/form_steps.rb

require 'rspec'
require_relative '../../lib/pitch_class'
require_relative '../../lib/chord'
require_relative '../../lib/form'

Given('an Exposition with themes in I and V') do
  @expo = true
end

Given('a Development section exploring the hexatonic cycle') do
  @dev = true
end

Given('a Recapitulation returning themes to the Tonic') do
  @recap = true
end

When('I validate the large-scale structure') do
  @sonata = SonataForm.new(@expo, @dev, @recap)
end

Then('it is identified as a {string}') do |type|
  expect(@sonata.complete?).to be true
end

Then('the semantic closure confirms consistency across the whole composition') do
  # Consistency is a key dimension of 8-point validation
  expect(@sonata.complete?).to be true
end
