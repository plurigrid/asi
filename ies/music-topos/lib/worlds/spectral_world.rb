# lib/worlds/spectral_world.rb
require_relative '../worlds'
require_relative '../spectral'

class SpectralWorld < MusicalWorlds::World
  def initialize
    # Metric: Distance between fundamental frequencies
    metric = lambda do |s1, s2|
      (s1.fundamental - s2.fundamental).abs
    end
    super("Spectral World", metric)
  end
end
