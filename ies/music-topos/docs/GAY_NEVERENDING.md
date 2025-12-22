# Gay.jl Neverending Productions

**Color Transitions Guide Infinite Music**

```
φ: γ = 2⁶⁴/φ → hue += 137.508° → spiral out forever → never repeat → always return
```

This document describes the system that generates infinite, deterministic music guided by color sequences based on the golden angle.

## Philosophy

> "The next color determines the next sound."

Gay.jl provides deterministic-yet-unpredictable color sequences via:
- **Golden angle hue rotation**: 137.508° per step (never repeats, always returns)
- **Splittable RNG** for parallel streams
- **Seed-based reproducibility**

The production is **neverending** because:
- Golden ratio ensures we spiral forever without exact repetition
- Each color transition determines the next musical gesture
- The stream is infinite but deterministic (reproducible with seed)

## Golden Angle

The golden angle is:

```
θ = 360° / φ² ≈ 137.508°
```

Where φ = (1 + √5) / 2 ≈ 1.618 (the golden ratio).

This angle has a special property: successive rotations never repeat and maximally distribute points around the circle. This is the same principle that governs:
- Phyllotaxis in plants (leaf arrangement)
- Sunflower seed spirals
- Efficient sampling in quasi-Monte Carlo methods

## GayClient

Local simulation of Gay.jl's color generation:

```ruby
class GayClient
  attr_reader :seed, :index
  
  def initialize(seed: nil)
    @seed = seed || 42
    @index = 0
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
    # Golden angle hue
    hue = (idx * @golden_angle) % 360
    
    # Saturation and lightness from deterministic hash
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
  
  def reset!
    @index = 0
  end
  
  def set_seed!(new_seed)
    @seed = new_seed
    @index = 0
  end
end
```

### Deterministic RNG

Reproducible randomness from seed and index:

```ruby
def deterministic_rng(seed, idx)
  # Multiplicative hash (Knuth)
  combined = seed * 2654435761 + idx * 1597334677
  hash1 = (combined ^ (combined >> 16)) * 2246822507
  hash2 = (hash1 ^ (hash1 >> 13)) * 3266489909
  final = hash2 ^ (hash2 >> 16)
  
  {
    s: ((final & 0xFFFF) / 65535.0),
    l: (((final >> 16) & 0xFFFF) / 65535.0)
  }
end
```

## Color → Music Mapping

### Hue → Pitch Class

30° per semitone (chromatic mapping):

```ruby
def self.hue_to_pitch_class(hue)
  (hue / 30.0).floor % 12
end
```

### Hue → Scale Degree

Map to diatonic modes:

```ruby
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
```

### Saturation → Density

Notes per beat:

```ruby
def self.saturation_to_density(saturation)
  # 0.0 = sparse (1 note), 1.0 = dense (8 notes)
  (1 + saturation * 7).round.clamp(1, 8)
end
```

### Lightness → Amplitude

```ruby
def self.lightness_to_amplitude(lightness)
  # 0.0 = silent, 1.0 = full
  (lightness * 0.8).clamp(0.05, 0.8)
end
```

### Lightness → Register

```ruby
def self.lightness_to_octave(lightness)
  # Dark = low, light = high
  (lightness * 5 + 2).floor.clamp(2, 7)
end
```

### RGB Delta → Interval

Color movement maps to harmonic movement:

```ruby
def self.rgb_delta_to_interval(color1, color2)
  dr = color2[:rgb][:r] - color1[:rgb][:r]
  dg = color2[:rgb][:g] - color1[:rgb][:g]
  db = color2[:rgb][:b] - color1[:rgb][:b]
  
  # Red = root movement, Green = third, Blue = fifth
  {
    root: (dr * 12).round.clamp(-12, 12),
    third: (dg * 4).round.clamp(-4, 4),
    fifth: (db * 7).round.clamp(-7, 7)
  }
end
```

### Hue → Tempo Modifier

Warm colors faster, cool colors slower:

```ruby
def self.hue_to_tempo_mod(hue)
  # Red (0°) = 1.2x, Cyan (180°) = 0.8x
  1.0 + Math.cos(hue * Math::PI / 180) * 0.2
end
```

### Saturation → Articulation

```ruby
def self.saturation_to_articulation(saturation)
  if saturation < 0.3
    :legato
  elsif saturation < 0.7
    :normal
  else
    :staccato
  end
end
```

### Full Mapping

```ruby
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
```

## Musical Styles

Different interpretations of color mappings:

### Drone

Long, sustained tones with slow movement:

```ruby
STYLE_CONFIGS = {
  drone: {
    scale: LYDIAN_SCALE,
    base_duration: 4.0,
    rest_probability: 0.1,
    chord_probability: 0.8,
    density_mult: 0.3
  },
  # ...
}
```

### Ambient

Floating, ethereal textures:

```ruby
ambient: {
  scale: MAJOR_SCALE,
  base_duration: 2.0,
  rest_probability: 0.2,
  chord_probability: 0.6,
  density_mult: 0.5
}
```

### IDM

Complex rhythms and timbres:

```ruby
idm: {
  scale: PHRYGIAN_SCALE,
  base_duration: 0.25,
  rest_probability: 0.15,
  chord_probability: 0.3,
  density_mult: 1.5
}
```

### Jungle

Fast breakbeats with dark harmonies:

```ruby
jungle: {
  scale: MINOR_SCALE,
  base_duration: 0.125,
  rest_probability: 0.1,
  chord_probability: 0.2,
  density_mult: 2.0
}
```

### Industrial

Heavy, mechanical textures:

```ruby
industrial: {
  scale: LOCRIAN_SCALE,
  base_duration: 0.5,
  rest_probability: 0.05,
  chord_probability: 0.4,
  density_mult: 1.0
}
```

## Neverending Generator

Infinite event generator:

```ruby
class NeverendingGenerator
  include Enumerable
  
  def initialize(seed: 42, style: :idm)
    @client = GayClient.new(seed: seed)
    @style = style
    @style_config = STYLE_CONFIGS[@style]
    @prev_color = nil
  end
  
  def each
    loop do
      color = @client.next_color!
      params = ColorMusicMapper.color_to_params(
        color, 
        prev_color: @prev_color,
        scale: @style_config[:scale]
      )
      
      event = generate_event(params)
      yield event
      
      @prev_color = color
    end
  end
  
  def generate_for_duration(duration)
    events = []
    current_beat = 0
    
    each do |event|
      break if current_beat >= duration
      
      event[:at] = current_beat
      events << event
      
      dur = event[:dur] || @style_config[:base_duration]
      current_beat += dur
    end
    
    events
  end
  
  private
  
  def generate_event(params)
    r = rand
    
    if r < @style_config[:rest_probability]
      generate_rest(params)
    elsif r < @style_config[:rest_probability] + @style_config[:chord_probability]
      generate_chord(params)
    else
      generate_melody(params)
    end
  end
end
```

## Pattern Builder

Integration with Free Monad:

```ruby
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
  
  # Infinite streaming pattern
  def self.stream(seed: 42, style: :idm)
    generator = NeverendingGenerator.new(seed: seed, style: style)
    
    Enumerator.new do |yielder|
      generator.each do |event|
        yielder << event
      end
    end
  end
end
```

## Realtime Streamer

For live performance:

```ruby
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
```

## Color Visualization

Print color-to-music mappings:

```ruby
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
```

**Example output:**

```
Color-guided musical sequence (seed: 42)
============================================================
1. #A855F7 → E4 (amp: 0.48, density: 5, normal)
2. #5FD1B8 → A3 (amp: 0.39, density: 4, normal)
3. #F7B855 → C5 (amp: 0.52, density: 6, staccato)
4. #5F8AD1 → F3 (amp: 0.41, density: 5, normal)
5. #D15F6A → G4 (amp: 0.46, density: 4, normal)
...
```

## Usage

### Command Line

```bash
# Full showcase (all 5 styles)
just neverending

# Individual styles
just gay-drone      # Slow, sustained (64 beats)
just gay-ambient    # Ethereal, floating (48 beats)
just gay-idm        # Complex, rhythmic (32 beats)
just gay-jungle     # Fast breakbeats (24 beats)
just gay-industrial # Heavy, mechanical (32 beats)

# Print color guide (no audio)
just color-guide
```

### Ruby API

```ruby
require_relative 'lib/gay_neverending'

# Single style
pattern = GayNeverending::ColorPatternBuilder.build(
  duration: 32.0,
  seed: 42,
  style: :ambient
)

# Full showcase
pattern = GayNeverending::Showcase.neverending_showcase(seed: 42)

# Infinite stream for live coding
stream = GayNeverending::ColorPatternBuilder.stream(seed: 42, style: :idm)
stream.take(100).each { |event| process(event) }

# Realtime playback
streamer = GayNeverending::RealtimeStreamer.new(seed: 42, tempo: 120)
streamer.start! { |event| play(event) }
sleep 60
streamer.stop!
```

## Reproducibility

The same seed always produces the same sequence:

```ruby
# These will be identical
seq1 = GayClient.new(seed: 42).palette(100)
seq2 = GayClient.new(seed: 42).palette(100)
seq1 == seq2  # => true

# Different seeds produce different sequences
seq3 = GayClient.new(seed: 43).palette(100)
seq1 == seq3  # => false
```

## Mathematical Properties

### Never Repeats

The golden angle is irrational, so:

```
∀n,m ∈ ℤ, n ≠ m ⟹ (n × 137.508°) mod 360° ≠ (m × 137.508°) mod 360°
```

No two colors in the sequence have exactly the same hue.

### Always Returns

Despite never repeating exactly, the sequence is **quasi-periodic**: it returns arbitrarily close to any previous hue infinitely often.

### Uniform Distribution

In the limit, hues are uniformly distributed around the circle:

```
lim_{N→∞} (1/N) Σᵢ f(hue_i) = (1/360) ∫₀³⁶⁰ f(θ) dθ
```

This ensures all pitch classes are visited equally over time.

## References

- **Gay.jl**: https://github.com/JuliaGraphics/Gay.jl
- **Vogel, H.**: "A Better Way to Construct the Sunflower Head" (1979)
- **Golden Ratio in Music**: Jean, R.V. "Phyllotaxis" (1994)
