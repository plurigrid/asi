# lib/form.rb
require_relative 'structure'

class MusicalForm
  def self.analyze(phrases)
    # Simple AA'B structure detection
    return :unknown if phrases.size < 2
    
    # Placeholder for formal logic
    :period
  end
end

class SonataForm
  attr_reader :exposition, :development, :recapitulation

  def initialize(expo, dev, recap)
    @exposition = expo
    @development = dev
    @recapitulation = recap
  end

  def complete?
    @exposition && @development && @recapitulation
  end
end
