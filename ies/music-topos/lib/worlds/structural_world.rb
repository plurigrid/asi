# lib/worlds/structural_world.rb
require_relative '../worlds'
require_relative '../structure'

class StructuralWorld < MusicalWorlds::World
  def initialize
    # Metric: Binary - 0 if same cadence type, 1 if different
    metric = lambda do |p1, p2|
      p1.cadence == p2.cadence ? 0 : 1
    end
    super("Structural World (Phrases)", metric)
  end
end
