#!/usr/bin/env ruby
# spec/spec_helper.rb
# Test configuration and shared setup for Music Topos RSpec tests

require 'rspec'
require 'socket'

# Load all lib files
$LOAD_PATH.unshift(File.expand_path('../lib', __dir__))

# Load core musical structures
require 'pitch_class'
require 'chord'
require 'harmonic_function'
require 'harmony'
require 'tonality'
require 'form'
require 'worlds/world'
require 'worlds/initial_object_world'
require 'worlds/terminal_object_world'

# Configure RSpec
RSpec.configure do |config|
  config.color = true
  config.formatter = :documentation
end

# Shared test utilities
module MusicalTestHelpers
  def create_test_pitch_class(value = 0)
    PitchClass.new(value)
  end

  def create_test_chord(root_value = 0)
    Chord.new(PitchClass.new(root_value))
  end

  def create_test_harmonic_function(root_value = 0, function_type = HarmonicFunction::TONIC)
    chord = create_test_chord(root_value)
    HarmonicFunction.new(chord, function_type, 'C')
  end
end

RSpec.configure do |config|
  config.include MusicalTestHelpers
end
