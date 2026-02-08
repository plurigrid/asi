# lib/worlds/progression_world.rb
require_relative '../worlds'
require_relative '../progressions'

class ProgressionWorld < MusicalWorlds::World
  def initialize
    # Metric: Levenshtein-style distance between progressions
    metric = lambda do |p1, p2|
      # Simplified: number of different chords
      (p1.size - (p1 & p2).size).abs
    end
    super("Progression World", metric)
  end
end
