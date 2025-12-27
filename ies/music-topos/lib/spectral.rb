# lib/spectral.rb
class Spectrum
  attr_reader :fundamental, :partials

  def initialize(fundamental, num_partials = 8)
    @fundamental = fundamental
    @partials = (1..num_partials).map { |n| fundamental * n }
  end

  def in_hz
    @partials
  end

  def in_midi
    @partials.map { |hz| 12 * Math.log2(hz / 440.0) + 69 }
  end
end
