# lib/worlds/form_world.rb
require_relative '../worlds'
require_relative '../form'

class FormWorld < MusicalWorlds::World
  def initialize
    # Metric: Distance between formal structures
    metric = lambda do |f1, f2|
      f1 == f2 ? 0 : 2
    end
    super("Form World", metric)
  end
end
