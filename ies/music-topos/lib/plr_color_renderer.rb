#!/usr/bin/env ruby
# lib/plr_color_renderer.rb
#
# PLR Color Renderer: Bridge between LCH color space and Sonic Pi
#
# Maps learnable color gamut (from Julia) to MIDI pitches and synthesis parameters:
# - H (Hue, 0-360°) → MIDI pitch (C1-C7)
# - L (Lightness, 0-100) → Amplitude (0-1)
# - C (Chroma, 0-130) → Duration and timbre
#
# Integrates with:
# - Neo-Riemannian transforms (PLR)
# - Harmonic function analysis (T/S/D)
# - SonicPiRenderer (OSC output)

require_relative 'sonic_pi_renderer'
require_relative 'neo_riemannian'
require_relative 'harmonic_function'
require_relative 'chord'
require_relative 'pitch_class'

class PLRColorRenderer
  # Color space boundaries
  HUE_MIN = 0.0
  HUE_MAX = 360.0
  LIGHTNESS_MIN = 0.0
  LIGHTNESS_MAX = 100.0
  CHROMA_MIN = 0.0
  CHROMA_MAX = 130.0

  # MIDI pitch range (C1 to C7)
  MIDI_MIN = 24
  MIDI_MAX = 108
  MIDI_RANGE = MIDI_MAX - MIDI_MIN

  # Timing and amplitude ranges
  DURATION_MIN = 0.25
  DURATION_MAX = 4.0
  AMPLITUDE_MIN = 0.1
  AMPLITUDE_MAX = 1.0

  attr_reader :renderer, :key_context

  def initialize(synth: :prophet, duration_factor: 1.0, key_context: 'C')
    @renderer = SonicPiRenderer.new(synth: synth, duration_factor: duration_factor)
    @key_context = key_context
    @color_to_chord_cache = {}
  end

  # =========================================================================
  # Color → MIDI Pitch Mapping
  # =========================================================================

  # Convert LCH color (Hash or NamedTuple) to MIDI note number
  # H (Hue) determines the pitch class (0-360° → C to B)
  def color_to_midi_note(color)
    hue = extract_hue(color)

    # Map hue to pitch class (0-11)
    # 0° = C, 30° = C#, 60° = D, ... 330° = B
    pitch_class_index = (hue / 30.0).round % 12

    # Map to MIDI (assuming octave 4 as default, can vary by lightness)
    midi_note = 60 + pitch_class_index  # C4 (60) as reference

    # Clamp to valid MIDI range
    [[midi_note, MIDI_MIN].max, MIDI_MAX].min
  end

  # Convert Lightness to amplitude (0-100 → 0.1-1.0)
  def color_to_amplitude(color)
    lightness = extract_lightness(color)
    normalized = lightness / LIGHTNESS_MAX
    AMPLITUDE_MIN + (normalized * (AMPLITUDE_MAX - AMPLITUDE_MIN))
  end

  # Convert Chroma to duration (0-130 → 0.25-4.0 seconds)
  def color_to_duration(color)
    chroma = extract_chroma(color)
    normalized = chroma / CHROMA_MAX
    DURATION_MIN + (normalized * (DURATION_MAX - DURATION_MIN))
  end

  # =========================================================================
  # Color → Harmonic Function Analysis
  # =========================================================================

  # Analyze harmonic function of a color based on hue zones
  # Hue zones map to functional harmony:
  # T (Tonic):      330-90°  (reds, warm)
  # S (Subdominant): 90-210° (greens, cool)
  # D (Dominant):   210-330° (blues, active)
  def color_to_function(color)
    hue = extract_hue(color)

    case hue
    when 330...360, 0...90     # Reds and warm tones
      HarmonicFunction::TONIC
    when 90...210              # Greens and cool-neutral tones
      HarmonicFunction::SUBDOMINANT
    when 210...330             # Blues and active tones
      HarmonicFunction::DOMINANT
    else
      HarmonicFunction::TONIC  # Default
    end
  end

  # =========================================================================
  # Color → Chord Generation
  # =========================================================================

  # Convert a color to a chord by analyzing hue and mapping to scale degrees
  def color_to_chord(color)
    # Check cache first
    cache_key = color_cache_key(color)
    return @color_to_chord_cache[cache_key] if @color_to_chord_cache.key?(cache_key)

    hue = extract_hue(color)

    # Map hue to scale degree (0-360° → 0-6 for 7-note scale)
    # Assuming C major scale: C D E F G A B
    scale_degrees = [0, 2, 4, 5, 7, 9, 11]  # Interval pattern (semitones)
    degree = (hue / 60.0).round % 7
    root_semitone = scale_degrees[degree]

    # Get key root
    key_root = key_to_semitone(@key_context)
    midi_root = 60 + ((key_root + root_semitone) % 12)

    # Create triad (root + major third + fifth)
    root = PitchClass.from_midi(midi_root)
    third = PitchClass.from_midi(midi_root + 4)
    fifth = PitchClass.from_midi(midi_root + 7)

    chord = Chord.new(root, third, fifth)
    @color_to_chord_cache[cache_key] = chord
    chord
  end

  # =========================================================================
  # PLR Transformations on Colors
  # =========================================================================

  # Apply PLR transformation to color (returns modified color)
  def apply_plr_to_color(color, plr_type)
    case plr_type
    when :P  # Parallel: Hue ±15°
      apply_plr_parallel(color)
    when :L  # Leading-tone: Lightness ±10
      apply_plr_leading_tone(color)
    when :R  # Relative: Chroma ±20, Hue ±30°
      apply_plr_relative(color)
    else
      color
    end
  end

  private def apply_plr_parallel(color)
    hue = extract_hue(color)
    # Determine direction based on current hue
    # +15° for first half, -15° for second half (toggle)
    new_hue = if hue < 180
                (hue + 15) % 360.0
              else
                (hue - 15 + 360.0) % 360.0
              end
    set_hue(color, new_hue)
  end

  private def apply_plr_leading_tone(color)
    lightness = extract_lightness(color)
    new_lightness = if lightness < LIGHTNESS_MAX / 2
                      lightness + 10
                    else
                      lightness - 10
                    end
    new_lightness = [[new_lightness, LIGHTNESS_MIN].max, LIGHTNESS_MAX].min
    set_lightness(color, new_lightness)
  end

  private def apply_plr_relative(color)
    hue = extract_hue(color)
    chroma = extract_chroma(color)
    new_hue = (hue + 30) % 360.0
    new_chroma = if chroma < CHROMA_MAX / 2
                   chroma + 20
                 else
                   chroma - 20
                 end
    new_chroma = [[new_chroma, CHROMA_MIN].max, CHROMA_MAX].min
    color_with_updates(color, hue: new_hue, chroma: new_chroma)
  end

  # =========================================================================
  # Rendering to Sonic Pi
  # =========================================================================

  # Render a single color as a sound event
  def render_color(color, duration_override: nil)
    midi_note = color_to_midi_note(color)
    amplitude = color_to_amplitude(color)
    duration = duration_override || color_to_duration(color)

    @renderer.send_osc_message(
      '/trigger/prophet',
      midi_note.to_i,
      amplitude.to_f,
      duration.to_f
    )
  end

  # Render a sequence of colors (temporal progression)
  def render_color_sequence(colors, interval: 1.0)
    colors.each do |color|
      render_color(color, duration_override: interval * 0.9)
      sleep(interval)
    end
  end

  # Render PLR progression (P-L-P-L-P-L hexatonic)
  def render_hexatonic_from_color(color, interval: 1.0)
    current = color
    6.times do |i|
      render_color(current, duration_override: interval * 0.9)
      current = apply_plr_to_color(current, i.even? ? :P : :L)
      sleep(interval)
    end
  end

  # Render harmonic cadence from color
  # Authentic: D→T (210-330° → 330-90°)
  # Plagal: S→T (90-210° → 330-90°)
  # Deceptive: D→S (210-330° → 90-210°)
  def render_cadence(cadence_type: :authentic, interval: 1.0)
    start_color = case cadence_type
                  when :authentic
                    { L: 60.0, C: 50.0, H: 270.0 }  # D zone (blue)
                  when :plagal
                    { L: 60.0, C: 50.0, H: 150.0 }  # S zone (green)
                  when :deceptive
                    { L: 60.0, C: 50.0, H: 270.0 }  # D zone
                  else
                    { L: 60.0, C: 50.0, H: 0.0 }    # Default
                  end

    colors = case cadence_type
             when :authentic
               # D(dominant) → T(tonic): 270° → 0°
               [
                 start_color,
                 apply_plr_to_color(start_color, :R),  # Move toward T
                 { L: 70.0, C: 60.0, H: 0.0 }          # T (red) resolution
               ]
             when :plagal
               # S(subdominant) → T(tonic): 150° → 0°
               [
                 start_color,
                 apply_plr_to_color(start_color, :L),  # Move toward T
                 { L: 70.0, C: 60.0, H: 0.0 }          # T resolution
               ]
             when :deceptive
               # D(dominant) → S(subdominant): 270° → 150°
               [
                 start_color,
                 apply_plr_to_color(start_color, :P),  # Move toward S
                 { L: 60.0, C: 55.0, H: 150.0 }        # S (green)
               ]
             else
               [start_color]
             end

    render_color_sequence(colors, interval: interval)
  end

  # =========================================================================
  # Chord Generation from Colors
  # =========================================================================

  # Generate a chord progression from a sequence of colors
  def colors_to_chord_progression(colors)
    colors.map { |color| color_to_chord(color) }
  end

  # =========================================================================
  # Helper Methods
  # =========================================================================

  private

  def extract_hue(color)
    case color
    when Hash
      color[:H] || color['H'] || 0.0
    else  # NamedTuple or object with . accessor
      color.H || 0.0
    end
  end

  def extract_lightness(color)
    case color
    when Hash
      color[:L] || color['L'] || 50.0
    else
      color.L || 50.0
    end
  end

  def extract_chroma(color)
    case color
    when Hash
      color[:C] || color['C'] || 50.0
    else
      color.C || 50.0
    end
  end

  def set_hue(color, new_hue)
    case color
    when Hash
      color.merge(H: new_hue)
    else
      # Assume NamedTuple-like with replace method or reconstruct
      if color.respond_to?(:to_h)
        h = color.to_h
        h[:H] = new_hue
        h
      else
        color
      end
    end
  end

  def set_lightness(color, new_lightness)
    case color
    when Hash
      color.merge(L: new_lightness)
    else
      if color.respond_to?(:to_h)
        h = color.to_h
        h[:L] = new_lightness
        h
      else
        color
      end
    end
  end

  def color_with_updates(color, hue: nil, chroma: nil)
    case color
    when Hash
      updates = {}
      updates[:H] = hue if hue
      updates[:C] = chroma if chroma
      color.merge(updates)
    else
      if color.respond_to?(:to_h)
        h = color.to_h
        h[:H] = hue if hue
        h[:C] = chroma if chroma
        h
      else
        color
      end
    end
  end

  def color_cache_key(color)
    h = extract_hue(color)
    l = extract_lightness(color)
    c = extract_chroma(color)
    "#{h.round(1)}_#{l.round(1)}_#{c.round(1)}"
  end

  def key_to_semitone(key_str)
    case key_str.upcase
    when 'C'  then 0
    when 'G'  then 7
    when 'D'  then 2
    when 'A'  then 9
    when 'E'  then 4
    when 'B'  then 11
    when 'F'  then 5
    when 'BB' then 10
    when 'EB' then 3
    when 'AB' then 8
    else 0
    end
  end
end
