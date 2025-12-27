# sonic_pi_rubato_bridge.rb
# Mazzola's Topos of Music → Sonic Pi via RubatoBridge
#
# Demonstrates:
# - Form/Denotator categorical structure
# - Gay.jl color-guided composition (seed 1069)
# - Rubato tempo deformation (φ₂ from Vol. II)
# - Performance formula: Score × Tempo × Dynamics × Articulation
#
# Run with: sonic_pi < .topos/sonic_pi_rubato_bridge.rb
# Or paste into Sonic Pi GUI

use_bpm 120

# Gay.jl SplitMix64 color generation (deterministic)
define :splitmix64 do |state|
  z = (state + 0x9e3779b97f4a7c15) & 0xFFFFFFFFFFFFFFFF
  z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & 0xFFFFFFFFFFFFFFFF
  z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & 0xFFFFFFFFFFFFFFFF
  z ^ (z >> 31)
end

define :color_at do |seed, index|
  state = seed
  index.times do
    state = splitmix64(state)
  end
  splitmix64(state)
end

define :pitch_from_color do |color_value|
  # Map to MIDI range 48-84 (C3 to C6)
  hue = (color_value & 0xFFFF) * 360.0 / 65536.0
  48 + (hue / 360.0 * 36).to_i
end

define :duration_from_color do |color_value|
  # Map saturation byte to duration 0.25-1.5 beats
  sat = ((color_value >> 16) & 0xFF) / 255.0
  0.25 + sat * 1.25
end

# Mazzola's rubato tempo deformation (φ₂)
define :rubato do |onset, base_tempo, amplitude, period|
  phase = onset * Math::PI * 2 / period + 0.618  # Golden ratio phase
  deviation = amplitude * Math.sin(phase)
  base_tempo * (1.0 + deviation)
end

# Performance formula: Dynamics
define :dynamics do |velocity|
  Math.log(velocity + 1) / Math.log(128)  # Logarithmic envelope
end

# =============================================================================
# SEED 1069: The Shared Pattern
# Balanced ternary: [+1, -1, -1, +1, +1, +1, +1]
# =============================================================================

seed = 1069
n_notes = 12
base_tempo = 120
rubato_amplitude = 0.15
rubato_period = 4.0

puts "RUBATO BRIDGE: Mazzola → Sonic Pi"
puts "  Seed: #{seed}"
puts "  Notes: #{n_notes}"
puts "  Rubato amplitude: #{rubato_amplitude}"
puts ""

# =============================================================================
# COMPOSE: Color-guided score with Rubato tempo
# =============================================================================

live_loop :rubato_composition do
  n_notes.times do |i|
    # Get color-guided parameters
    color = color_at(seed, i)
    pitch = pitch_from_color(color)
    base_dur = duration_from_color(color)

    # Apply Mazzola's performance formula
    onset = i * 0.5
    tempo_factor = rubato(onset, 1.0, rubato_amplitude, rubato_period)
    actual_dur = base_dur / tempo_factor

    # Dynamics with slight variation
    velocity = 70 + (i % 4) * 10
    amp = dynamics(velocity)

    # Articulation (legato vs staccato)
    articulation = 0.85 + (i % 3) * 0.05
    sustain_dur = actual_dur * articulation

    # Play the note
    synth :piano, note: pitch, sustain: sustain_dur, amp: amp

    # Visual feedback
    puts "Note #{i}: pitch=#{pitch} dur=#{actual_dur.round(2)} amp=#{amp.round(2)} tempo_factor=#{tempo_factor.round(2)}"

    sleep actual_dur
  end

  # Pause before repeating
  sleep 2
  stop  # Remove this line for infinite loop
end

# =============================================================================
# DRONE: Color-guided bass drone (WallpaperRubette equivalent)
# =============================================================================

in_thread do
  4.times do |i|
    color = color_at(seed + 1000, i)
    bass_pitch = pitch_from_color(color) - 24  # Two octaves down

    synth :dark_ambience, note: bass_pitch, sustain: 3, amp: 0.3
    sleep 3
  end
end

# =============================================================================
# TEXTURE: Maximum dynamism layer (BigBangRubette equivalent)
# =============================================================================

in_thread do
  sleep 0.5  # Offset

  8.times do |i|
    # High entropy pitch selection
    color = color_at(seed * 2, i * 3)
    pitch = pitch_from_color(color) + 12  # One octave up

    # Chaotic duration
    dur = 0.125 + rand(0.25)

    synth :blade, note: pitch, sustain: dur * 0.5, amp: 0.15, cutoff: 80
    sleep dur
  end
end
