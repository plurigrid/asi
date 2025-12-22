# lib/sonic_pi_renderer.rb
require 'socket'

class SonicPiRenderer
  attr_reader :synth, :duration_factor

  # Standard ports:
  # 4559: User OSC (requires live_loop sync in Sonic Pi)
  # 4557: Server OSC (direct code execution, "God Mode", legacy/internal)
  def initialize(synth: :sine, duration_factor: 1.0, use_osc: true)
    @synth = synth
    @duration_factor = duration_factor
    @use_osc = use_osc
    
    if @use_osc
      begin
        @client = UDPSocket.new
        # We target the User OSC port by default as it's the intended public interface
        # Found active on port 4560 via lsof
        @port = 4560
        @client.connect('127.0.0.1', @port)
      rescue => e
        puts "Warning: Could not connect to Sonic Pi: #{e.message}"
        @use_osc = false
      end
    end
  end

  def play_pitch_class(pitch_class, octave, duration)
    midi_note = pitch_class.to_midi(octave)
    send_osc_message('/trigger/prophet', midi_note, duration * @duration_factor)
  end

  def play_chord(chord, octaves, duration)
    # Send all notes in one bundle or separate messages
    chord.voices.each_with_index do |voice, idx|
       oct = octaves[idx] || 4
       play_pitch_class(voice, oct, duration)
    end
  end

  def play_composition(chords, octaves)
    chords.each do |chord|
      play_chord(chord, octaves, 1.0)
      sleep(1.0 * @duration_factor)
    end
  end

  # =========================================================================
  # Color-to-Sound Rendering (LCH → MIDI)
  # =========================================================================

  # Play a color as a sound event
  # color: Hash or object with :H, :L, :C keys (LCH color space)
  # H (Hue, 0-360°) → MIDI pitch (24-108)
  # L (Lightness, 0-100) → Amplitude (0.1-1.0)
  # C (Chroma, 0-130) → Duration (0.25-4.0s)
  def play_color(color, duration_override: nil)
    hue = extract_color_value(color, :H)
    lightness = extract_color_value(color, :L)
    chroma = extract_color_value(color, :C)

    # H → MIDI note (map 0-360° to MIDI 24-108)
    midi_note = hue_to_midi_note(hue)

    # L → Amplitude (0-100 → 0.1-1.0)
    amplitude = lightness_to_amplitude(lightness)

    # C → Duration (0-130 → 0.25-4.0s)
    duration = chroma_to_duration(chroma)
    duration = duration_override if duration_override

    send_osc_message('/trigger/prophet', midi_note.to_i, amplitude.to_f, duration.to_f)
  end

  # Play a sequence of colors with timing
  def play_color_sequence(colors, interval: 1.0)
    colors.each do |color|
      play_color(color, duration_override: interval * 0.9)
      sleep(interval * @duration_factor)
    end
  end

  # Play harmonic cadence from colors
  def play_color_cadence(cadence_colors, interval: 1.0)
    cadence_colors.each do |color|
      play_color(color, duration_override: interval * 0.9)
      sleep(interval * @duration_factor)
    end
  end

  # Robust OSC Packet Construction
  def send_osc_message(path, *args)
    return unless @use_osc && @client
    
    # 1. OSC Address Pattern (Must be null-terminated and padded to 4 bytes)
    msg = osc_pad_string(path)
    
    # 2. OSC Type Tag String (comma + tags, null-terminated, padded)
    types = ","
    args.each do |arg|
      case arg
      when Integer then types << "i"
      when Float   then types << "f"
      when String  then types << "s"
      end
    end
    msg << osc_pad_string(types)
    
    # 3. OSC Arguments
    args.each do |arg|
      case arg
      when Integer
        msg << [arg].pack("N") # 32-bit big-endian integer
      when Float
        msg << [arg].pack("g") # 32-bit big-endian float
      when String
        msg << osc_pad_string(arg)
      end
    end
    
    @client.send(msg, 0)
  rescue => e
    puts "Error sending OSC: #{e.message}"
  end

  private

  # Pads a string with nulls to the next multiple of 4 bytes
  # Crucial: String MUST be null-terminated first
  def osc_pad_string(str)
    s = str.dup.b
    s << "\x00" # Null terminator
    padding = (4 - (s.length % 4)) % 4
    s << "\x00" * padding
    s
  end

  # =========================================================================
  # Color-to-Sound Helper Methods
  # =========================================================================

  # Extract value from color (Hash or object)
  def extract_color_value(color, key)
    case color
    when Hash
      color[key] || color[key.to_s] || 0.0
    else
      # Try object accessor
      color.respond_to?(key) ? color.send(key) : 0.0
    end
  end

  # Convert hue (0-360°) to MIDI note (24-108, C1 to C7)
  def hue_to_midi_note(hue)
    hue_normalized = hue % 360.0
    midi_min = 24
    midi_max = 108
    midi_min + ((hue_normalized / 360.0) * (midi_max - midi_min))
  end

  # Convert lightness (0-100) to amplitude (0.1-1.0)
  def lightness_to_amplitude(lightness)
    normalized = [lightness / 100.0, 0.0, 1.0].sort[1]  # Clamp to [0, 1]
    0.1 + (normalized * 0.9)  # Map to [0.1, 1.0]
  end

  # Convert chroma (0-130) to duration (0.25-4.0 seconds)
  def chroma_to_duration(chroma)
    normalized = [chroma / 130.0, 0.0, 1.0].sort[1]  # Clamp to [0, 1]
    0.25 + (normalized * 3.75)  # Map to [0.25, 4.0]
  end
end
