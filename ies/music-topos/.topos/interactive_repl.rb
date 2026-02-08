#!/usr/bin/env ruby

# bin/interactive_repl.rb
#
# INTERACTIVE REPL: Real-time composition and exploration
# Compose → Validate → Play → Perceive → Refine (simultaneously)
#
# Commands:
#   play <chord_spec>     - Render chord to audio
#   progress <chords...>  - Render progression
#   validate <spec>       - Check semantic closure
#   plr <chord> <op>      - Apply PLR transformation
#   world <type>          - Show world structure
#   help                  - Show all commands
#   quit                  - Exit

require_relative '../lib/pitch_class'
require_relative '../lib/chord'
require_relative '../lib/neo_riemannian'
require_relative '../lib/worlds'
require_relative '../lib/ontological_validator'
require_relative '../lib/audio_synthesis'

class InteractiveRepl
  def initialize
    @synthesis = AudioSynthesis.new(output_file: '/tmp/interactive_composition.wav')
    @last_chord = nil
    @composition_history = []
  end

  def run
    puts "=" * 80
    puts "🎵 MUSIC TOPOS INTERACTIVE REPL"
    puts "=" * 80
    puts ""
    puts "Real-time composition with ontological validation"
    puts "Type 'help' for commands"
    puts ""

    loop do
      print "> "
      input = gets.chomp.strip

      break if input == 'quit'
      next if input.empty?

      process_command(input)
    end

    puts ""
    puts "✓ Session closed"
  end

  private

  def process_command(input)
    parts = input.split
    command = parts[0].downcase

    case command
    when 'play'
      play_command(parts[1..].join(' '))
    when 'progress'
      progress_command(parts[1..].join(' '))
    when 'validate'
      validate_command(parts[1..].join(' '))
    when 'plr'
      plr_command(parts[1], parts[2])
    when 'world'
      world_command(parts[1])
    when 'help'
      show_help
    when 'history'
      show_history
    when 'metric'
      metric_command(parts[1], parts[2])
    else
      puts "? Unknown command: #{command}"
    end
  rescue => e
    puts "✗ Error: #{e.message}"
  end

  def play_command(chord_spec)
    chord = parse_chord(chord_spec)
    puts ""
    puts "Playing: #{chord}"

    # Validate before rendering
    composition = { notes: chord.voices, chords: [chord] }
    closure = OntologicalValidator.semantic_closure(composition)

    if closure[:closed]
      puts "✓ Semantic closure verified (#{closure[:summary][:valid_dimensions]}/8 dimensions)"

      # Render to audio
      puts "Rendering audio..."
      octaves = [4, 3, 3, 2]
      frequencies = chord.to_frequencies(octaves)

      puts "Frequencies: #{frequencies.map { |f| f.round(2) }.join(', ')} Hz"
      puts "MIDI notes: #{chord.to_midi_notes(octaves).join(', ')}"

      # For now, just show what would play
      puts "✓ Audio would play (implement OSC to Sonic Pi for actual sound)"
    else
      puts "✗ Semantic closure FAILED"
      failed = closure[:closure_points].select { |_, v| !v }
      puts "Failed dimensions: #{failed.keys.join(', ')}"
    end

    @last_chord = chord
    @composition_history << chord
  end

  def progress_command(chord_specs)
    chord_strings = chord_specs.split(',').map(&:strip)
    chords = chord_strings.map { |s| parse_chord(s) }

    puts ""
    puts "Composition:"
    chords.each_with_index do |chord, idx|
      puts "  #{idx + 1}. #{chord}"
    end

    # Validate entire composition
    composition = {
      notes: chords.flat_map(&:voices),
      chords: chords
    }

    closure = OntologicalValidator.semantic_closure(composition)

    if closure[:closed]
      puts ""
      puts "✓ PROGRESSION VALID"
      puts "  Semantic closure: #{closure[:summary][:valid_dimensions]}/8 dimensions"

      # Analyze voice leading
      puts ""
      puts "Voice leading analysis:"
      chords.each_cons(2) do |from, to|
        metric = from.voice_leading_distance(to)
        smooth = from.smoothness_score(to)
        puts "  #{from} → #{to}: #{metric[:total]} semitones, smoothness #{(smooth[:score]*100).round(1)}%"
      end
    else
      puts ""
      puts "✗ PROGRESSION INVALID"
      failed = closure[:closure_points].select { |_, v| !v }
      puts "  Failed: #{failed.keys.join(', ')}"
    end

    @last_chord = chords.last
    @composition_history.concat(chords)
  end

  def validate_command(spec)
    chord = parse_chord(spec)
    composition = { notes: chord.voices, chords: [chord] }

    puts ""
    puts "Validating: #{chord}"
    puts ""

    # Full validation
    existence = OntologicalValidator.validate_existence(composition)
    closure = OntologicalValidator.semantic_closure(composition)
    consistency = OntologicalValidator.logical_consistency(composition)

    puts "EXISTENCE:"
    puts "  Valid: #{existence[:exists]}"

    puts ""
    puts "SEMANTIC CLOSURE (8 dimensions):"
    closure[:closure_points].each do |dim, valid|
      status = valid ? "✓" : "✗"
      puts "  #{status} #{dim}: #{valid}"
    end

    puts ""
    puts "LOGICAL CONSISTENCY:"
    puts "  Valid: #{consistency[:consistent]}"
    puts "  Errors: #{consistency[:error_count]}"

    puts ""
    if existence[:exists] && closure[:closed] && consistency[:consistent]
      puts "✓ COMPOSITION IS MATHEMATICALLY VALID"
    else
      puts "✗ COMPOSITION FAILS VALIDATION"
    end
  end

  def plr_command(chord_spec, operation)
    chord = parse_chord(chord_spec)
    operation_name = operation.upcase

    puts ""
    puts "Applying #{operation_name} to #{chord}"

    transformed = case operation_name
                  when 'P'
                    NeoRiemannian.parallel(chord)
                  when 'R'
                    NeoRiemannian.relative(chord)
                  when 'L'
                    NeoRiemannian.leading_tone_exchange(chord)
                  else
                    raise "Unknown operation: #{operation_name}"
                  end

    puts "Result: #{transformed}"

    metric = chord.voice_leading_distance(transformed)
    smoothness = chord.smoothness_score(transformed)

    puts ""
    puts "Voice leading:"
    puts "  Distance: #{metric[:total]} semitones"
    puts "  Smoothness: #{(smoothness[:score] * 100).round(1)}%"
    puts "  Type: #{metric[:parsimonious] ? 'Parsimonious ✓' : 'Disjunct'}"

    @last_chord = transformed
    @composition_history << transformed
  end

  def world_command(world_type)
    puts ""

    case world_type&.downcase
    when 'pitch'
      world = MusicalWorlds.pitch_space_world
      puts "Pitch Space World (S¹)"
      puts "  Objects: Pitch classes (ℝ/12ℤ)"
      puts "  Metric: Circle distance"
      puts "  Axiom: d(a,b) = min(|a-b|, 12-|a-b|)"

    when 'chord'
      world = MusicalWorlds.chord_space_world
      puts "Chord Space World (Tⁿ)"
      puts "  Objects: Chords (points on tori)"
      puts "  Metric: Manhattan distance"
      puts "  Axiom: Voice leading on toroidal surface"

    when 'harmonic'
      world = MusicalWorlds::HarmonicWorld.world
      puts "Harmonic Function World (T-S-D)"
      puts "  Objects: Functions {T, S, D}"
      puts "  Morphisms: Allowed progressions"
      puts "  Structure: Categorical"

    when 'transformation'
      world = MusicalWorlds::TransformationWorld.world
      puts "Transformation World (S₃)"
      puts "  Objects: Group elements {id, P, R, L, PR, RL}"
      puts "  Operations: PLR group"
      puts "  Structure: |S₃| = 6"

    when nil
      puts "Available worlds: pitch, chord, harmonic, transformation"

    else
      puts "? Unknown world: #{world_type}"
    end
  end

  def metric_command(chord1_spec, chord2_spec)
    return unless chord1_spec && chord2_spec

    chord1 = parse_chord(chord1_spec)
    chord2 = parse_chord(chord2_spec)

    puts ""
    puts "Distance from #{chord1} to #{chord2}:"

    metric = chord1.voice_leading_distance(chord2)
    smoothness = chord1.smoothness_score(chord2)

    puts "  Total motion: #{metric[:total]} semitones"
    puts "  Smoothness: #{(smoothness[:score] * 100).round(1)}%"
    puts "  Type: #{metric[:parsimonious] ? 'Parsimonious' : 'Disjunct'}"

    puts ""
    puts "Voice movements:"
    metric[:movements].each_with_index do |move, idx|
      voice_name = ['Soprano', 'Alto', 'Tenor', 'Bass'][idx]
      puts "  #{voice_name}: #{move[:from].note_name} → #{move[:to].note_name} (#{move[:distance]} semitones)"
    end
  end

  def show_help
    puts ""
    puts "COMMANDS:"
    puts "  play <CHORD>           Play a single chord"
    puts "  progress <C1>,<C2>...  Play a chord progression"
    puts "  validate <CHORD>       Check semantic closure"
    puts "  plr <CHORD> <OP>       Apply P, R, or L transformation"
    puts "  metric <C1> <C2>       Compute distance between chords"
    puts "  world <TYPE>           Show world structure"
    puts "  history                Show composition history"
    puts "  help                   This help"
    puts "  quit                   Exit"
    puts ""
    puts "CHORD FORMAT:"
    puts "  [Note] [Note] [Note]   e.g., 'C E G' or 'C E G C' (4-voice)"
    puts ""
    puts "NOTES: C, C#, D, D#, E, F, F#, G, G#, A, A#, B"
    puts ""
  end

  def show_history
    puts ""
    puts "Composition history (#{@composition_history.size} chords):"
    @composition_history.each_with_index do |chord, idx|
      puts "  #{idx + 1}. #{chord}"
    end
  end

  def parse_chord(chord_spec)
    notes = chord_spec.split.map(&:strip)
    Chord.from_notes(notes)
  rescue => e
    raise "Invalid chord specification: #{chord_spec} - #{e.message}"
  end
end

# Run REPL
repl = InteractiveRepl.new
repl.run
