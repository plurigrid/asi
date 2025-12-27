# lib/gay_neverending.rb
#
# NEVERENDING PRODUCTIONS via Gay.jl Color Transitions
#
# ============================================================================
# PHILOSOPHY
# ============================================================================
#
# "The next color determines the next sound."
#
# Gay.jl provides deterministic-yet-unpredictable color sequences via:
# - Golden angle hue rotation: 137.508° per step (never repeats, always returns)
# - Splittable RNG for parallel streams
# - Seed-based reproducibility
#
# Musical mapping:
#   HUE (0-360°)     → Pitch class (0-11) + register offset
#   SATURATION (0-1) → Density / note count / harmonic complexity
#   LIGHTNESS (0-1)  → Amplitude / dynamics
#   RGB deltas       → Melodic intervals / harmonic movement
#
# The production is NEVERENDING because:
# - Golden ratio ensures we spiral forever without exact repetition
# - Each color transition determines the next musical gesture
# - The stream is infinite but deterministic (reproducible with seed)
#
# ============================================================================

require_relative 'free_monad'
require_relative 'maximum_dynamism'
require_relative 'jungle_involution'
require 'net/http'
require 'json'
require 'uri'

module GayNeverending
  extend FreeMonad::DSL
  
  # ============================================================================
  # GAY.JL MCP CLIENT
  # ============================================================================
  
  class GayClient
    attr_reader :seed, :index
    
    def initialize(seed: nil)
      @seed = seed || 42
      @index = 0
      @color_cache = []
      @http_available = false  # Will use local simulation
      
      # Precompute golden angle colors locally (matching Gay.jl algorithm)
      @phi = (1 + Math.sqrt(5)) / 2
      @golden_angle = 360.0 / (@phi ** 2)  # ≈ 137.508°
    end
    
    # Get next color (advances stream)
    def next_color!
      @index += 1
      color_at(@index)
    end
    
    # Get color at specific index without advancing
    def color_at(idx)
      # Gay.jl golden angle algorithm
      hue = (idx * @golden_angle) % 360
      
      # Saturation and lightness from splittable RNG
      # Using deterministic hash based on seed + index
      rng_state = deterministic_rng(@seed, idx)
      saturation = 0.5 + (rng_state[:s] * 0.4)  # 0.5-0.9
      lightness = 0.4 + (rng_state[:l] * 0.3)   # 0.4-0.7
      
      # Convert HSL to RGB
      rgb = hsl_to_rgb(hue, saturation, lightness)
      
      {
        index: idx,
        hue: hue,
        saturation: saturation,
        lightness: lightness,
        rgb: rgb,
        hex: rgb_to_hex(rgb)
      }
    end
    
    # Get N colors starting from current position
    def palette(n)
      n.times.map { next_color! }
    end
    
    # Golden thread: colors along the golden spiral
    def golden_thread(steps)
      steps.times.map { |i| color_at(@index + i + 1) }
    end
    
    # Reset to beginning
    def reset!
      @index = 0
    end
    
    # Set seed (restarts sequence)
    def set_seed!(new_seed)
      @seed = new_seed
      @index = 0
    end
    
    private
    
    def deterministic_rng(seed, idx)
      # Simple but effective deterministic hash
      combined = seed * 2654435761 + idx * 1597334677
      hash1 = (combined ^ (combined >> 16)) * 2246822507
      hash2 = (hash1 ^ (hash1 >> 13)) * 3266489909
      final = hash2 ^ (hash2 >> 16)
      
      {
        s: ((final & 0xFFFF) / 65535.0),
        l: (((final >> 16) & 0xFFFF) / 65535.0)
      }
    end
    
    def hsl_to_rgb(h, s, l)
      c = (1 - (2 * l - 1).abs) * s
      x = c * (1 - ((h / 60.0) % 2 - 1).abs)
      m = l - c / 2
      
      r, g, b = case (h / 60).floor % 6
        when 0 then [c, x, 0]
        when 1 then [x, c, 0]
        when 2 then [0, c, x]
        when 3 then [0, x, c]
        when 4 then [x, 0, c]
        when 5 then [c, 0, x]
        else [0, 0, 0]
      end
      
      { r: r + m, g: g + m, b: b + m }
    end
    
    def rgb_to_hex(rgb)
      r = (rgb[:r] * 255).round.clamp(0, 255)
      g = (rgb[:g] * 255).round.clamp(0, 255)
      b = (rgb[:b] * 255).round.clamp(0, 255)
      "#%02X%02X%02X" % [r, g, b]
    end
  end
  
  # ============================================================================
  # COLOR → MUSIC MAPPING
  # ============================================================================
  
  class ColorMusicMapper
    # Hue to pitch class (chromatic)
    def self.hue_to_pitch_class(hue)
      (hue / 30.0).floor % 12  # 30° per semitone
    end
    
    # Hue to scale degree (diatonic)
    MAJOR_SCALE = [0, 2, 4, 5, 7, 9, 11]
    MINOR_SCALE = [0, 2, 3, 5, 7, 8, 10]
    DORIAN_SCALE = [0, 2, 3, 5, 7, 9, 10]
    PHRYGIAN_SCALE = [0, 1, 3, 5, 7, 8, 10]
    LYDIAN_SCALE = [0, 2, 4, 6, 7, 9, 11]
    MIXOLYDIAN_SCALE = [0, 2, 4, 5, 7, 9, 10]
    LOCRIAN_SCALE = [0, 1, 3, 5, 6, 8, 10]
    
    def self.hue_to_scale_degree(hue, scale: DORIAN_SCALE)
      degree_index = ((hue / 360.0) * scale.length).floor % scale.length
      scale[degree_index]
    end
    
    # Saturation to density (notes per beat)
    def self.saturation_to_density(saturation)
      # 0.0 = sparse (1 note), 1.0 = dense (8 notes)
      (1 + saturation * 7).round.clamp(1, 8)
    end
    
    # Lightness to amplitude
    def self.lightness_to_amplitude(lightness)
      # 0.0 = silent, 1.0 = full
      (lightness * 0.8).clamp(0.05, 0.8)
    end
    
    # Lightness to register (octave)
    def self.lightness_to_octave(lightness)
      # Dark = low, light = high
      (lightness * 5 + 2).floor.clamp(2, 7)
    end
    
    # RGB delta to interval
    def self.rgb_delta_to_interval(color1, color2)
      dr = color2[:rgb][:r] - color1[:rgb][:r]
      dg = color2[:rgb][:g] - color1[:rgb][:g]
      db = color2[:rgb][:b] - color1[:rgb][:b]
      
      # Map color movement to musical interval
      # Red = root movement, Green = third movement, Blue = fifth movement
      root_move = (dr * 12).round.clamp(-12, 12)
      third_move = (dg * 4).round.clamp(-4, 4)  # ±major/minor 3rd
      fifth_move = (db * 7).round.clamp(-7, 7)  # ±fifth
      
      { root: root_move, third: third_move, fifth: fifth_move }
    end
    
    # Hue to tempo modifier
    def self.hue_to_tempo_mod(hue)
      # Warm colors = faster, cool colors = slower
      # Red (0°) = 1.2x, Cyan (180°) = 0.8x
      1.0 + Math.cos(hue * Math::PI / 180) * 0.2
    end
    
    # Saturation to articulation
    def self.saturation_to_articulation(saturation)
      # Low sat = legato, high sat = staccato
      if saturation < 0.3
        :legato
      elsif saturation < 0.7
        :normal
      else
        :staccato
      end
    end
    
    # Full color to musical parameters
    def self.color_to_params(color, prev_color: nil, scale: DORIAN_SCALE)
      pitch_class = hue_to_scale_degree(color[:hue], scale: scale)
      octave = lightness_to_octave(color[:lightness])
      midi_pitch = 12 * octave + pitch_class
      
      params = {
        pitch: midi_pitch.clamp(24, 96),
        amplitude: lightness_to_amplitude(color[:lightness]),
        density: saturation_to_density(color[:saturation]),
        articulation: saturation_to_articulation(color[:saturation]),
        tempo_mod: hue_to_tempo_mod(color[:hue]),
        color: color
      }
      
      if prev_color
        params[:interval] = rgb_delta_to_interval(prev_color, color)
      end
      
      params
    end
  end
  
  # ============================================================================
  # NEVERENDING GENERATOR
  # ============================================================================
  
  class NeverendingGenerator
    attr_reader :client, :events_generated, :current_params
    
    def initialize(seed: 42, style: :ambient)
      @client = GayClient.new(seed: seed)
      @style = style
      @events_generated = 0
      @prev_color = nil
      @current_params = nil
      @history = []
      
      # Style-specific parameters
      @style_config = style_config(style)
    end
    
    def style_config(style)
      case style
      when :ambient
        {
          base_duration: 2.0,
          density_mult: 0.3,
          tempo: 60,
          scale: ColorMusicMapper::LYDIAN_SCALE,
          chord_probability: 0.7,
          rest_probability: 0.2
        }
      when :jungle
        {
          base_duration: 0.125,
          density_mult: 2.0,
          tempo: 172,
          scale: ColorMusicMapper::PHRYGIAN_SCALE,
          chord_probability: 0.1,
          rest_probability: 0.05
        }
      when :industrial
        {
          base_duration: 0.25,
          density_mult: 1.5,
          tempo: 130,
          scale: ColorMusicMapper::LOCRIAN_SCALE,
          chord_probability: 0.3,
          rest_probability: 0.1
        }
      when :idm
        {
          base_duration: 0.1,
          density_mult: 1.0,
          tempo: 145,
          scale: ColorMusicMapper::DORIAN_SCALE,
          chord_probability: 0.4,
          rest_probability: 0.15
        }
      when :drone
        {
          base_duration: 8.0,
          density_mult: 0.1,
          tempo: 40,
          scale: ColorMusicMapper::MAJOR_SCALE,
          chord_probability: 0.9,
          rest_probability: 0.3
        }
      else
        # Default / experimental
        {
          base_duration: 0.5,
          density_mult: 1.0,
          tempo: 120,
          scale: ColorMusicMapper::DORIAN_SCALE,
          chord_probability: 0.5,
          rest_probability: 0.1
        }
      end
    end
    
    # Generate next musical event based on next color
    def next_event!
      color = @client.next_color!
      params = ColorMusicMapper.color_to_params(
        color,
        prev_color: @prev_color,
        scale: @style_config[:scale]
      )
      
      @current_params = params
      @prev_color = color
      @events_generated += 1
      
      # Determine event type based on color + style
      if rand < @style_config[:rest_probability]
        generate_rest(params)
      elsif rand < @style_config[:chord_probability]
        generate_chord(params)
      else
        generate_melody(params)
      end
    end
    
    # Generate N events
    def generate(n)
      n.times.map { next_event! }
    end
    
    # Infinite enumerator
    def each
      return enum_for(:each) unless block_given?
      loop { yield next_event! }
    end
    
    # Generate events for duration (in beats)
    def generate_for_duration(total_beats)
      events = []
      current_beat = 0
      
      while current_beat < total_beats
        event = next_event!
        event[:at] = current_beat
        events << event
        
        # Calculate duration for this event
        dur = case event[:type]
        when :rest, :chord
          event[:dur] || 0.5
        when :melody
          event[:notes]&.sum { |n| n[:dur] || 0.1 } || 0.5
        else
          0.5
        end
        
        current_beat += dur
      end
      
      events
    end
    
    private
    
    def generate_rest(params)
      duration = @style_config[:base_duration] * (0.5 + rand * 1.5)
      {
        type: :rest,
        dur: duration,
        color: params[:color][:hex]
      }
    end
    
    def generate_chord(params)
      density = [(params[:density] * @style_config[:density_mult]).round, 1].max
      density = [density, 6].min
      
      # Build chord from pitch
      root = params[:pitch]
      pitches = [root]
      
      # Add intervals based on color
      if params[:interval]
        pitches << root + params[:interval][:third] if density > 1
        pitches << root + params[:interval][:fifth] if density > 2
      else
        pitches << root + 4 if density > 1  # Major 3rd
        pitches << root + 7 if density > 2  # Perfect 5th
      end
      
      # Additional density notes
      (density - 3).times do |i|
        pitches << root + [9, 11, 14, 16, 19][i % 5]
      end
      
      pitches = pitches.map { |p| p.clamp(24, 96) }.uniq
      
      duration = @style_config[:base_duration] * params[:tempo_mod]
      duration *= case params[:articulation]
        when :staccato then 0.5
        when :legato then 1.5
        else 1.0
      end
      
      {
        type: :chord,
        pitches: pitches,
        dur: duration,
        amplitude: params[:amplitude],
        color: params[:color][:hex]
      }
    end
    
    def generate_melody(params)
      density = [(params[:density] * @style_config[:density_mult]).round, 1].max
      
      base_pitch = params[:pitch]
      notes = []
      
      density.times do |i|
        # Melodic movement from color
        offset = if params[:interval]
          (params[:interval][:root] * (i + 1) / density.to_f).round
        else
          [-2, -1, 0, 1, 2, 3, 5, 7].sample
        end
        
        pitch = (base_pitch + offset).clamp(24, 96)
        dur = @style_config[:base_duration] / density * params[:tempo_mod]
        amp = params[:amplitude] * (1 - i * 0.1)
        
        notes << { pitch: pitch, dur: dur, amplitude: amp }
      end
      
      {
        type: :melody,
        notes: notes,
        color: params[:color][:hex]
      }
    end
  end
  
  # ============================================================================
  # PATTERN BUILDER (Free Monad integration)
  # ============================================================================
  
  class ColorPatternBuilder
    extend FreeMonad::DSL
    
    def self.build(duration: 32.0, seed: 42, style: :ambient)
      generator = NeverendingGenerator.new(seed: seed, style: style)
      events = generator.generate_for_duration(duration)
      
      pattern_events = events.flat_map do |event|
        case event[:type]
        when :rest
          [rest!(event[:dur])]
        when :chord
          [play_chord!(event[:pitches], event[:dur], event[:amplitude])]
        when :melody
          event[:notes].map { |n| play_note!(n[:pitch], n[:dur], n[:amplitude]) }
        end
      end
      
      sequence!(*pattern_events)
    end
    
    # Build infinite streaming pattern (returns enumerator)
    def self.stream(seed: 42, style: :idm)
      generator = NeverendingGenerator.new(seed: seed, style: style)
      
      Enumerator.new do |yielder|
        generator.each do |event|
          case event[:type]
          when :rest
            yielder << { type: :rest, dur: event[:dur], color: event[:color] }
          when :chord
            yielder << { 
              type: :chord, 
              pitches: event[:pitches], 
              dur: event[:dur],
              amplitude: event[:amplitude],
              color: event[:color]
            }
          when :melody
            event[:notes].each do |n|
              yielder << {
                type: :note,
                pitch: n[:pitch],
                dur: n[:dur],
                amplitude: n[:amplitude],
                color: event[:color]
              }
            end
          end
        end
      end
    end
  end
  
  # ============================================================================
  # REALTIME STREAMER
  # ============================================================================
  
  class RealtimeStreamer
    def initialize(seed: 42, style: :idm, tempo: 120)
      @generator = NeverendingGenerator.new(seed: seed, style: style)
      @tempo = tempo
      @running = false
    end
    
    def start!(&block)
      @running = true
      beat_duration = 60.0 / @tempo
      
      Thread.new do
        @generator.each do |event|
          break unless @running
          
          yield event if block_given?
          
          sleep_time = (event[:dur] || 0.5) * beat_duration
          sleep(sleep_time)
        end
      end
    end
    
    def stop!
      @running = false
    end
  end
  
  # ============================================================================
  # SHOWCASE
  # ============================================================================
  
  class Showcase
    extend FreeMonad::DSL
    
    def self.neverending_showcase(seed: 42)
      sequence!(
        section_marker("╔══════════════════════════════════════╗"),
        section_marker("║     NEVERENDING PRODUCTIONS          ║"),
        section_marker("║  Guided by Gay.jl Color Transitions  ║"),
        section_marker("║  φ: γ=2⁶⁴/φ → hue+=137.508°          ║"),
        section_marker("╚══════════════════════════════════════╝"),
        rest!(0.3),
        
        section_marker("=== STYLE: DRONE (seed: #{seed}) ==="),
        ColorPatternBuilder.build(duration: 16.0, seed: seed, style: :drone),
        rest!(0.5),
        
        section_marker("=== STYLE: AMBIENT (seed: #{seed + 1}) ==="),
        ColorPatternBuilder.build(duration: 16.0, seed: seed + 1, style: :ambient),
        rest!(0.5),
        
        section_marker("=== STYLE: IDM (seed: #{seed + 2}) ==="),
        ColorPatternBuilder.build(duration: 12.0, seed: seed + 2, style: :idm),
        rest!(0.5),
        
        section_marker("=== STYLE: JUNGLE (seed: #{seed + 3}) ==="),
        ColorPatternBuilder.build(duration: 8.0, seed: seed + 3, style: :jungle),
        rest!(0.5),
        
        section_marker("=== STYLE: INDUSTRIAL (seed: #{seed + 4}) ==="),
        ColorPatternBuilder.build(duration: 10.0, seed: seed + 4, style: :industrial)
      )
    end
    
    def self.single_style(duration: 32.0, seed: 42, style: :idm)
      ColorPatternBuilder.build(duration: duration, seed: seed, style: style)
    end
    
    # Print color sequence as it would guide music
    def self.print_color_guide(n: 20, seed: 42)
      client = GayClient.new(seed: seed)
      
      puts "Color-guided musical sequence (seed: #{seed})"
      puts "=" * 60
      
      prev_color = nil
      n.times do |i|
        color = client.next_color!
        params = ColorMusicMapper.color_to_params(color, prev_color: prev_color)
        
        note_name = %w[C C# D D# E F F# G G# A A# B][params[:pitch] % 12]
        octave = params[:pitch] / 12 - 1
        
        puts "#{i+1}. #{color[:hex]} → #{note_name}#{octave} " \
             "(amp: #{params[:amplitude].round(2)}, " \
             "density: #{params[:density]}, " \
             "#{params[:articulation]})"
        
        prev_color = color
      end
    end
    
    private
    
    def self.section_marker(name)
      FreeMonad::Pure.new(name)
    end
  end
end
