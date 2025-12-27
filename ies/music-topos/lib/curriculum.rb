# Curriculum compiler for music-topos
# Pure functions that compile curriculum sections into ScoreEvent arrays
# Mirrors src/music_topos/core.clj initial-world and terminal-world

require_relative 'score_event'

module MusicTopos
  module Curriculum
    INITIAL_WORLD = {
      name: "Initial Object World",
      pitch_classes: (60..71).to_a,
      harmonic_functions: [
        { name: "Tonic", root: 60, chord: [60, 64, 67] },
        { name: "Subdominant", root: 65, chord: [65, 69, 72] },
        { name: "Dominant", root: 67, chord: [67, 71, 74] }
      ],
      modulation_keys: [0, 7, 2, 5],
      chords: [
        { name: "C Major", notes: [60, 64, 67] },
        { name: "F Major", notes: [65, 69, 72] },
        { name: "G Major", notes: [67, 71, 74] }
      ],
      progression: [60, 65, 67, 60],
      cadences: [
        { name: "Authentic", notes: [67, 60] },
        { name: "Plagal", notes: [65, 60] },
        { name: "Half", notes: [60, 67] },
        { name: "Deceptive", notes: [67, 69] }
      ]
    }.freeze

    TERMINAL_WORLD = {
      name: "Terminal Object World (Sonata Form)",
      structure: {
        exposition: { key: 60, themes: [[60, 64, 67], [67, 71, 74]] },
        development: { keys: [65, 69, 72, 74, 78, 81], exploration: true },
        recapitulation: { key: 60, return: true },
        coda: { cadence: [67, 60], duration: 2 }
      },
      fragments: {
        pitch_classes: (60..71).to_a,
        harmonic_functions: [
          { name: "Tonic", embedding: :all_sections },
          { name: "Subdominant", embedding: :development },
          { name: "Dominant", embedding: :all_sections }
        ],
        modulation_keys: [60, 67, 74, 65, 60],
        chords: [[60, 64, 67], [65, 69, 72], [67, 71, 74]],
        progression: [[60, 64, 67], [65, 69, 72], [67, 71, 74], [60, 64, 67]],
        cadences: [[67, 74, 60], [65, 69, 60], [60, 67], [67, 69]]
      }
    }.freeze

    class << self
      def pitch_class_events(start_beat, pitches, dur, gap)
        pitches.each_with_index.map do |pitch, idx|
          ScoreEvent.new(
            id: "pitch_class_#{idx}",
            at: start_beat + (idx * (dur + gap)),
            dur: dur,
            world_object: WorldObject.new(type: :pitch_space, value: pitch),
            audio: Audio.from_midi(pitch, amplitude: 0.2),
            meta: { section: :pitch_classes, index: idx }
          )
        end
      end

      def harmonic_function_events(start_beat, functions, dur, gap)
        functions.each_with_index.map do |func, idx|
          chord = func[:chord]
          ScoreEvent.new(
            id: "harmonic_#{func[:name].downcase}",
            at: start_beat + (idx * (dur + gap)),
            dur: dur,
            world_object: WorldObject.new(type: :chord_space, value: chord),
            audio: Audio.from_midi(chord, amplitude: 0.2),
            meta: { section: :harmonic_functions, name: func[:name], index: idx }
          )
        end
      end

      def modulation_events(start_beat, intervals, dur, gap)
        intervals.each_with_index.map do |interval, idx|
          pitch = 60 + interval
          ScoreEvent.new(
            id: "modulation_#{idx}",
            at: start_beat + (idx * (dur + gap)),
            dur: dur,
            world_object: WorldObject.new(type: :transformation_world, value: interval),
            audio: Audio.from_midi(pitch, amplitude: 0.25),
            meta: { section: :modulation, interval: interval, index: idx }
          )
        end
      end

      def chord_progression_events(start_beat, chords, dur, gap)
        chords.each_with_index.map do |chord, idx|
          notes = chord.is_a?(Hash) ? chord[:notes] : chord
          ScoreEvent.new(
            id: "chord_#{idx}",
            at: start_beat + (idx * (dur + gap)),
            dur: dur,
            world_object: WorldObject.new(type: :chord_space, value: notes),
            audio: Audio.from_midi(notes, amplitude: 0.2),
            meta: { section: :chord_progression, index: idx }
          )
        end
      end

      def compile_initial_world
        events = []
        beat = 0.0

        events.concat(pitch_class_events(beat, INITIAL_WORLD[:pitch_classes], 0.08, 0.02))
        beat += INITIAL_WORLD[:pitch_classes].size * 0.1 + 0.5

        events.concat(harmonic_function_events(beat, INITIAL_WORLD[:harmonic_functions], 0.8, 0.4))
        beat += INITIAL_WORLD[:harmonic_functions].size * 1.2 + 0.5

        events.concat(modulation_events(beat, INITIAL_WORLD[:modulation_keys], 0.5, 0.1))

        events
      end

      def compile_terminal_world
        events = []
        beat = 0.0
        structure = TERMINAL_WORLD[:structure]

        events.concat(chord_progression_events(beat, structure[:exposition][:themes], 0.8, 0.2))
        beat += structure[:exposition][:themes].size * 1.0 + 0.5

        events.concat(chord_progression_events(beat, structure[:development][:keys].map { |k| [k] }, 0.3, 0.1))
        beat += structure[:development][:keys].size * 0.4 + 0.5

        events.concat(chord_progression_events(beat, [[structure[:recapitulation][:key], structure[:recapitulation][:key] + 4, structure[:recapitulation][:key] + 7]], 1.0, 0.2))
        beat += 1.2

        cadence = structure[:coda][:cadence]
        events.concat(chord_progression_events(beat, [[cadence[0]], [cadence[1]]], 1.0, 0.5))

        events
      end

      def compile_full_curriculum
        initial_events = compile_initial_world
        initial_duration = initial_events.map { |e| e.at + e.dur }.max + 1.0

        terminal_events = compile_terminal_world.map do |e|
          ScoreEvent.new(
            id: e.id,
            at: e.at + initial_duration,
            dur: e.dur,
            world_object: e.world_object,
            audio: e.audio,
            meta: e.meta
          )
        end

        initial_events + terminal_events
      end
    end
  end
end
