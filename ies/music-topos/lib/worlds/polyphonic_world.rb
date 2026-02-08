# lib/worlds/polyphonic_world.rb
require_relative '../worlds'
require_relative '../voice_leading'

class PolyphonicWorld < MusicalWorlds::World
  def initialize
    # Metric: sum of absolute midi note motions
    metric = lambda do |v1, v2|
      v1.zip(v2).map { |n1, n2| (n1 - n2).abs }.sum
    end
    super("Polyphonic World (SATB)", metric)
  end

  def add_satb(chord, octaves)
    midi_notes = chord.to_midi_notes(octaves)
    add_object(midi_notes)
  end
end
