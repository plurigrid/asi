#!/usr/bin/env ruby
# lib/skill_sonification.rb
#
# Skill Sonification: Audio mapping of skill availability across worlds
# ═══════════════════════════════════════════════════════════════════════════════
#
# "Cat the Poetic Engineer" - Maps categorical structures to sound
#
# Each skill becomes a voice:
# - Pitch: Derived from skill seed via golden angle (SPI-compliant)
# - Amplitude: Skill availability (0-1) across worlds
# - Duration: Skill complexity / depth
# - Timbre: TAP state (BACKFILL=sine, VERIFY=triangle, LIVE=saw)
#
# Each world becomes a harmonic layer:
# - Root frequency: World seed modulo 12 semitones
# - Chord quality: World type (major/minor/modal)
# - Dynamics: World activity level
#
# ═══════════════════════════════════════════════════════════════════════════════

require 'json'

module SkillSonification
  # Constants matching Gay.jl / SplitMix64
  GAY_SEED = 0x42D  # 1069
  GOLDEN_ANGLE = 137.508
  PHI = (1 + Math.sqrt(5)) / 2

  # Base frequencies (A4 = 440Hz, equal temperament)
  A4_HZ = 440.0

  # TAP states with waveform mappings
  TAP_STATES = {
    backfill: { value: -1, waveform: :sine, color: '#0000FF' },
    verify:   { value: 0,  waveform: :triangle, color: '#00FF00' },
    live:     { value: 1,  waveform: :saw, color: '#FF0000' }
  }

  # ═══════════════════════════════════════════════════════════════════════════
  # SplitMix64 (matches Gay.jl exactly)
  # ═══════════════════════════════════════════════════════════════════════════

  class SplitMix64
    MASK64 = 0xFFFFFFFFFFFFFFFF

    def initialize(seed)
      @state = seed & MASK64
    end

    def next_u64
      @state = (@state + 0x9E3779B97F4A7C15) & MASK64
      z = @state
      z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
      z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
      z ^ (z >> 31)
    end

    def next_float
      next_u64.to_f / MASK64.to_f
    end
  end

  # ═══════════════════════════════════════════════════════════════════════════
  # Skill Voice: Maps a skill to audio parameters
  # ═══════════════════════════════════════════════════════════════════════════

  class SkillVoice
    attr_reader :name, :seed, :pitch_hz, :amplitude, :duration_ms, :tap_state

    def initialize(name:, seed: nil, tap_state: :live)
      @name = name
      @seed = seed || name.hash & 0xFFFFFFFFFFFFFFFF
      @tap_state = tap_state
      @rng = SplitMix64.new(@seed)

      # Derive pitch from golden angle spiral (SPI-compliant)
      @pitch_index = @rng.next_u64 % 48  # 4 octaves
      @pitch_hz = pitch_from_index(@pitch_index)

      # Initial amplitude (will be modulated by world availability)
      @amplitude = 0.5

      # Duration based on skill complexity
      @duration_ms = 200 + (@rng.next_float * 800).to_i
    end

    # Calculate pitch using golden angle for maximum perceptual dispersion
    def pitch_from_index(index)
      # Map index to semitones via golden angle
      semitones = (index * GOLDEN_ANGLE / 30.0) % 48  # 4 octaves

      # Convert to frequency (A4 = 440Hz as reference)
      A4_HZ * (2 ** ((semitones - 24) / 12.0))
    end

    # Update amplitude based on availability in worlds
    def set_availability(availability_0_to_1)
      @amplitude = [0.0, [1.0, availability_0_to_1].min].max
    end

    # Get waveform type from TAP state
    def waveform
      TAP_STATES[@tap_state][:waveform]
    end

    # Convert to OSC message parameters
    def to_osc_params
      {
        freq: @pitch_hz,
        amp: @amplitude,
        dur: @duration_ms / 1000.0,
        wave: waveform,
        tap: TAP_STATES[@tap_state][:value]
      }
    end

    # Convert to SuperCollider SynthDef args
    def to_sc_args
      "\\freq, #{@pitch_hz.round(2)}, \\amp, #{@amplitude.round(3)}, " \
      "\\dur, #{@duration_ms / 1000.0}, \\tap, #{TAP_STATES[@tap_state][:value]}"
    end

    # Generate Sonic Pi code
    def to_sonic_pi
      wave_fn = case waveform
                when :sine then "synth :sine"
                when :triangle then "synth :tri"
                when :saw then "synth :saw"
                end

      "#{wave_fn}, note: #{midi_note}, amp: #{@amplitude.round(2)}, " \
      "sustain: #{@duration_ms / 1000.0}  # #{@name}"
    end

    def midi_note
      # Convert Hz to MIDI note number
      (69 + 12 * Math.log2(@pitch_hz / 440.0)).round
    end
  end

  # ═══════════════════════════════════════════════════════════════════════════
  # World Layer: Maps a world to harmonic parameters
  # ═══════════════════════════════════════════════════════════════════════════

  class WorldLayer
    attr_reader :name, :seed, :root_hz, :chord_type, :dynamics

    CHORD_TYPES = {
      pitch_space: :major,
      chord_space: :major7,
      harmonic_function: :dominant7,
      group_theory: :diminished,
      modulation: :augmented,
      polyphony: :suspended,
      progression: :major,
      structural: :modal,
      form: :modal,
      spectral: :cluster,
      computational: :tritone
    }

    def initialize(name:, seed: nil)
      @name = name
      @seed = seed || name.hash & 0xFFFFFFFFFFFFFFFF
      @rng = SplitMix64.new(@seed)

      # Root frequency: seed modulo 12 semitones from C2
      root_semitone = @seed % 12
      @root_hz = 65.41 * (2 ** (root_semitone / 12.0))  # C2 = 65.41 Hz

      # Chord type based on world category
      world_type = name.downcase.gsub(/[^a-z]/, '').to_sym
      @chord_type = CHORD_TYPES[world_type] || :major

      # Dynamics from RNG
      @dynamics = 0.3 + @rng.next_float * 0.5
    end

    # Get chord intervals for this world
    def chord_intervals
      case @chord_type
      when :major then [0, 4, 7]
      when :minor then [0, 3, 7]
      when :major7 then [0, 4, 7, 11]
      when :dominant7 then [0, 4, 7, 10]
      when :diminished then [0, 3, 6]
      when :augmented then [0, 4, 8]
      when :suspended then [0, 5, 7]
      when :modal then [0, 2, 7]
      when :cluster then [0, 1, 2]
      when :tritone then [0, 6]
      else [0, 4, 7]
      end
    end

    # Get frequencies for chord
    def chord_frequencies
      chord_intervals.map do |interval|
        @root_hz * (2 ** (interval / 12.0))
      end
    end

    # Convert to Sonic Pi code
    def to_sonic_pi
      notes = chord_intervals.map { |i| midi_root + i }
      "play_chord #{notes.inspect}, amp: #{@dynamics.round(2)}  # #{@name}"
    end

    def midi_root
      (69 + 12 * Math.log2(@root_hz / 440.0)).round
    end
  end

  # ═══════════════════════════════════════════════════════════════════════════
  # Skill Availability Matrix: Tracks which skills exist in which worlds
  # ═══════════════════════════════════════════════════════════════════════════

  class SkillAvailabilityMatrix
    attr_reader :skills, :worlds, :matrix

    def initialize
      @skills = {}  # name -> SkillVoice
      @worlds = {}  # name -> WorldLayer
      @matrix = {}  # [skill_name, world_name] -> availability (0-1)
    end

    def add_skill(name, seed: nil, tap_state: :live)
      @skills[name] = SkillVoice.new(name: name, seed: seed, tap_state: tap_state)
    end

    def add_world(name, seed: nil)
      @worlds[name] = WorldLayer.new(name: name, seed: seed)
    end

    def set_availability(skill_name, world_name, availability)
      @matrix[[skill_name, world_name]] = availability

      # Update skill amplitude based on total availability
      total = @worlds.keys.map { |w| @matrix[[skill_name, w]] || 0 }.sum
      avg = total / @worlds.size.to_f
      @skills[skill_name]&.set_availability(avg)
    end

    def availability(skill_name, world_name)
      @matrix[[skill_name, world_name]] || 0.0
    end

    # Calculate skill availability across all worlds
    def skill_presence(skill_name)
      @worlds.keys.map { |w| availability(skill_name, w) }
    end

    # Calculate world coverage (how many skills are available)
    def world_coverage(world_name)
      @skills.keys.map { |s| availability(s, world_name) }
    end

    # Generate summary statistics
    def summary
      {
        total_skills: @skills.size,
        total_worlds: @worlds.size,
        total_connections: @matrix.size,
        avg_availability: @matrix.values.sum / @matrix.size.to_f,
        most_available_skill: @skills.keys.max_by { |s| skill_presence(s).sum },
        richest_world: @worlds.keys.max_by { |w| world_coverage(w).sum }
      }
    end
  end

  # ═══════════════════════════════════════════════════════════════════════════
  # Sonification Generator: Produces audio code from matrix
  # ═══════════════════════════════════════════════════════════════════════════

  class SonificationGenerator
    def initialize(matrix)
      @matrix = matrix
    end

    # Generate Sonic Pi composition
    def to_sonic_pi
      lines = [
        "# Skill Availability Sonification",
        "# Generated from #{@matrix.skills.size} skills across #{@matrix.worlds.size} worlds",
        "# Cat the Poetic Engineer - Music Topos",
        "",
        "use_bpm 72",
        ""
      ]

      # World layers as background harmony
      lines << "# World Harmonic Layers"
      lines << "in_thread do"
      @matrix.worlds.each do |name, layer|
        lines << "  #{layer.to_sonic_pi}"
        lines << "  sleep 4"
      end
      lines << "end"
      lines << ""

      # Skills as melodic voices
      lines << "# Skill Voices (golden angle dispersed)"
      lines << "in_thread do"
      @matrix.skills.each do |name, voice|
        if voice.amplitude > 0.1
          lines << "  #{voice.to_sonic_pi}"
          lines << "  sleep 0.5"
        end
      end
      lines << "end"

      lines.join("\n")
    end

    # Generate OSC message sequence
    def to_osc_messages
      messages = []

      # World setup
      @matrix.worlds.each_with_index do |(name, layer), i|
        messages << {
          path: '/world/layer',
          args: [i, layer.root_hz, layer.dynamics, layer.chord_type.to_s]
        }
      end

      # Skill voices
      @matrix.skills.each_with_index do |(name, voice), i|
        messages << {
          path: '/skill/voice',
          args: [i, voice.pitch_hz, voice.amplitude, voice.duration_ms, voice.waveform.to_s]
        }
      end

      # Availability matrix
      @matrix.matrix.each do |(skill, world), availability|
        messages << {
          path: '/availability',
          args: [skill.to_s, world.to_s, availability]
        }
      end

      messages
    end

    # Generate JSON for external tools
    def to_json
      {
        metadata: {
          generated_at: Time.now.iso8601,
          seed: GAY_SEED,
          golden_angle: GOLDEN_ANGLE
        },
        skills: @matrix.skills.map do |name, voice|
          {
            name: name,
            pitch_hz: voice.pitch_hz,
            midi_note: voice.midi_note,
            amplitude: voice.amplitude,
            duration_ms: voice.duration_ms,
            tap_state: voice.tap_state,
            waveform: voice.waveform
          }
        end,
        worlds: @matrix.worlds.map do |name, layer|
          {
            name: name,
            root_hz: layer.root_hz,
            chord_type: layer.chord_type,
            chord_frequencies: layer.chord_frequencies,
            dynamics: layer.dynamics
          }
        end,
        availability: @matrix.matrix.map do |(skill, world), avail|
          { skill: skill, world: world, availability: avail }
        end,
        summary: @matrix.summary
      }.to_json
    end
  end

  # ═══════════════════════════════════════════════════════════════════════════
  # Factory: Create matrix from file system
  # ═══════════════════════════════════════════════════════════════════════════

  class MatrixFactory
    def self.from_filesystem(skills_dir:, worlds_dir:)
      matrix = SkillAvailabilityMatrix.new

      # Load skills
      Dir.glob(File.join(skills_dir, '**/SKILL.md')).each do |path|
        name = File.basename(File.dirname(path))
        content = File.read(path)

        # Determine TAP state from content keywords
        tap = if content.include?('self-rewriting') || content.include?('LIVE')
                :live
              elsif content.include?('verify') || content.include?('check')
                :verify
              else
                :backfill
              end

        matrix.add_skill(name, tap_state: tap)
      end

      # Load worlds
      Dir.glob(File.join(worlds_dir, '*.rb')).each do |path|
        name = File.basename(path, '.rb').gsub('_world', '')
        matrix.add_world(name)
      end

      # Calculate availability based on skill/world compatibility
      matrix.skills.keys.each do |skill|
        matrix.worlds.keys.each do |world|
          # Heuristic: compute compatibility via seed XOR and normalize
          skill_seed = matrix.skills[skill].seed
          world_seed = matrix.worlds[world].seed

          xor_dist = (skill_seed ^ world_seed).to_s(2).count('1')
          availability = 1.0 - (xor_dist / 64.0)  # Normalize to 0-1

          matrix.set_availability(skill, world, availability)
        end
      end

      matrix
    end

    # Create demo matrix
    def self.demo
      matrix = SkillAvailabilityMatrix.new

      # Skills
      ['glass-bead-game', 'world-hopping', 'epistemic-arbitrage',
       'codex-self-rewriting', 'frontend-design', 'gay-mcp',
       'bisimulation-game', 'geiser-chicken', 'hatchery-papers'].each do |skill|
        tap = skill.include?('self') ? :live : :verify
        matrix.add_skill(skill, tap_state: tap)
      end

      # Worlds
      ['pitch_space', 'chord_space', 'harmonic_function', 'group_theory',
       'modulation', 'polyphony', 'progression', 'structural',
       'form', 'spectral', 'computational'].each do |world|
        matrix.add_world(world)
      end

      # Set some example availabilities
      matrix.set_availability('glass-bead-game', 'harmonic_function', 0.9)
      matrix.set_availability('glass-bead-game', 'group_theory', 0.8)
      matrix.set_availability('world-hopping', 'modulation', 0.95)
      matrix.set_availability('world-hopping', 'form', 0.7)
      matrix.set_availability('codex-self-rewriting', 'computational', 1.0)
      matrix.set_availability('gay-mcp', 'spectral', 0.85)
      matrix.set_availability('bisimulation-game', 'group_theory', 0.9)
      matrix.set_availability('frontend-design', 'form', 0.6)

      matrix
    end
  end
end

# ═══════════════════════════════════════════════════════════════════════════════
# Main: Demo and CLI
# ═══════════════════════════════════════════════════════════════════════════════

if __FILE__ == $0
  puts "═══════════════════════════════════════════════════════════════════════"
  puts "  Skill Sonification: Cat the Poetic Engineer"
  puts "  Mapping skill availability to sound across worlds"
  puts "═══════════════════════════════════════════════════════════════════════"
  puts

  # Create matrix from command line or demo
  if ARGV[0] == '--from-fs' && ARGV[1] && ARGV[2]
    matrix = SkillSonification::MatrixFactory.from_filesystem(
      skills_dir: ARGV[1],
      worlds_dir: ARGV[2]
    )
  else
    matrix = SkillSonification::MatrixFactory.demo
  end

  generator = SkillSonification::SonificationGenerator.new(matrix)

  puts "Skills (#{matrix.skills.size}):"
  matrix.skills.each do |name, voice|
    puts "  #{name}: #{voice.pitch_hz.round(1)} Hz (MIDI #{voice.midi_note}), " \
         "amp=#{voice.amplitude.round(2)}, #{voice.tap_state}"
  end
  puts

  puts "Worlds (#{matrix.worlds.size}):"
  matrix.worlds.each do |name, layer|
    puts "  #{name}: #{layer.root_hz.round(1)} Hz root, #{layer.chord_type}"
  end
  puts

  puts "Summary:"
  summary = matrix.summary
  summary.each { |k, v| puts "  #{k}: #{v}" }
  puts

  puts "Sonic Pi Code:"
  puts "-" * 70
  puts generator.to_sonic_pi
  puts "-" * 70
  puts

  if ARGV.include?('--json')
    puts "JSON Output:"
    puts generator.to_json
  end
end
