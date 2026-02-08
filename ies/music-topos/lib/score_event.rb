# Shared ScoreEvent abstraction for music-topos curriculum
# Matches src/music_topos/score.clj for cross-language compatibility

module MusicTopos
  # Audio parameters for a score event
  Audio = Struct.new(:frequencies, :amplitude, :synth, keyword_init: true) do
    def self.from_midi(midi_notes, amplitude: 0.3, synth: :default)
      freqs = Array(midi_notes).map { |n| ScoreEvent.midi_to_hz(n) }
      new(frequencies: freqs, amplitude: amplitude, synth: synth)
    end
  end

  # World object types for categorical/topological spaces
  WORLD_OBJECT_TYPES = %i[
    pitch_space
    chord_space
    harmonic_world
    transformation_world
  ].freeze

  # A score event representing a moment in musical time
  # Shared schema with Clojure's music-topos.score/ScoreEvent
  ScoreEvent = Struct.new(:id, :at, :dur, :world_object, :audio, :meta, keyword_init: true) do
    def self.midi_to_hz(midi_note)
      440.0 * (2.0 ** ((midi_note - 69) / 12.0))
    end

    def self.beats_to_seconds(tempo, beats)
      (60.0 / tempo) * beats
    end

    def at_seconds(tempo)
      ScoreEvent.beats_to_seconds(tempo, at)
    end

    def dur_seconds(tempo)
      ScoreEvent.beats_to_seconds(tempo, dur)
    end

    def to_osc_bundle(tempo)
      {
        time: at_seconds(tempo),
        duration: dur_seconds(tempo),
        frequencies: audio&.frequencies || [],
        amplitude: audio&.amplitude || 0.3,
        synth: audio&.synth || :default
      }
    end

    def to_h
      {
        id: id,
        at: at,
        dur: dur,
        world_object: world_object,
        audio: audio&.to_h,
        meta: meta
      }
    end
  end

  # WorldObject wrapper for categorical structures
  WorldObject = Struct.new(:type, :value, :morphisms, keyword_init: true) do
    def initialize(type:, value:, morphisms: [])
      raise ArgumentError, "Unknown world type: #{type}" unless WORLD_OBJECT_TYPES.include?(type)
      super(type: type, value: value, morphisms: morphisms)
    end
  end
end
