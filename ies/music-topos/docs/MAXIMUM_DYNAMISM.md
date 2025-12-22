# Maximum Dynamism: Universal Derangement System

**Every Degree of Freedom Derangeable with Entropy**

This document describes the Maximum Dynamism system, which allows every component of every configuration to be perturbed with various entropy sources.

## Philosophy

> "Every component of every configuration of every in-stream action space degree of freedom is derangeable with randomness."

Maximum Dynamism transforms deterministic patterns into stochastic explorations by applying controlled perturbations to all musical parameters.

## Degrees of Freedom

| DOF | Description | Parameters |
|-----|-------------|------------|
| **Pitch** | Fundamental frequency | MIDI note, microtonal offset, octave displacement |
| **Time** | Temporal position | Onset, duration, tempo modulation |
| **Amplitude** | Loudness | Volume, dynamics, envelope |
| **Timbre** | Spectral content | Formants, harmonics (simulated via pitch) |
| **Structure** | Organization | Sequence order, repetition, branching |
| **Meta** | The parameters themselves | Intensity drift, strategy mutation |

## Entropy Sources

### Gaussian (Normal Distribution)

Bell curve around original value:

```ruby
def self.gaussian(mean: 0, stddev: 1)
  # Box-Muller transform
  u1 = rand
  u2 = rand
  z = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math::PI * u2)
  mean + z * stddev
end
```

**Use case:** Subtle humanization, natural variation

### Lévy Flight

Heavy-tailed distribution with rare large jumps:

```ruby
def self.levy(alpha: 1.5, scale: 1.0)
  # Mantegna's algorithm for Lévy stable
  u = rand * Math::PI - Math::PI / 2
  v = -Math.log(rand)
  
  scale * Math.sin(alpha * u) / (Math.cos(u) ** (1.0 / alpha)) *
    (Math.cos((1 - alpha) * u) / v) ** ((1 - alpha) / alpha)
end
```

**Use case:** Occasional dramatic pitch/duration jumps (Aphex Twin style)

### Logistic Map (Chaos)

Deterministic chaos from simple iteration:

```ruby
def self.logistic(x, r: 3.99)
  r * x * (1 - x)
end
```

**Use case:** Complex but reproducible patterns

### Lorenz Attractor

3D chaotic system:

```ruby
class LorenzAttractor
  def initialize(sigma: 10, rho: 28, beta: 8.0/3)
    @sigma, @rho, @beta = sigma, rho, beta
    @x, @y, @z = rand, rand, rand
    @dt = 0.01
  end
  
  def step
    dx = @sigma * (@y - @x)
    dy = @x * (@rho - @z) - @y
    dz = @x * @y - @beta * @z
    
    @x += dx * @dt
    @y += dy * @dt
    @z += dz * @dt
    
    [@x, @y, @z]
  end
  
  def next_value(coord: :x)
    step
    case coord
    when :x then @x / 20.0
    when :y then @y / 30.0
    when :z then (@z - 25) / 20.0
    end
  end
end
```

**Use case:** Slowly evolving, correlated parameter changes

### Drunk Walk (Brownian Motion)

Random walk with bounds:

```ruby
class DrunkWalk
  def initialize(step_size: 0.1, bounds: [-1, 1])
    @step_size = step_size
    @bounds = bounds
    @position = 0
  end
  
  def step
    @position += (rand - 0.5) * 2 * @step_size
    @position = @position.clamp(*@bounds)
  end
end
```

**Use case:** Gradual drift (Autechre pitch wander)

### Smooth Noise

Perlin-like continuous noise:

```ruby
class SmoothNoise
  def initialize(frequency: 0.1)
    @frequency = frequency
    @phase = rand * 1000
    @time = 0
  end
  
  def next_value
    @time += @frequency
    (Math.sin(@time + @phase) * 0.5 +
     Math.sin(@time * 2.1 + @phase * 1.3) * 0.3 +
     Math.sin(@time * 4.7 + @phase * 0.7) * 0.2)
  end
end
```

**Use case:** Organic, flowing modulation

## Derangement Configuration

### Configuration Structure

```ruby
class DerangementConfig
  attr_accessor :pitch, :duration, :amplitude, :onset, :structure, :meta
  
  def initialize(
    pitch: PitchDerangement.new,
    duration: DurationDerangement.new,
    amplitude: AmplitudeDerangement.new,
    onset: OnsetDerangement.new,
    structure: StructureDerangement.new,
    meta: MetaDerangement.new
  )
    @pitch = pitch
    @duration = duration
    @amplitude = amplitude
    @onset = onset
    @structure = structure
    @meta = meta
  end
end
```

### Pitch Derangement

```ruby
class PitchDerangement
  attr_accessor :enabled, :intensity, :strategy, :microtonal, :octave_displacement
  
  def initialize(
    enabled: true,
    intensity: 0.5,
    strategy: :gaussian,
    microtonal: false,
    octave_displacement: false
  )
    @enabled = enabled
    @intensity = intensity
    @strategy = strategy
    @microtonal = microtonal
    @octave_displacement = octave_displacement
  end
  
  def derange(pitch)
    return pitch unless @enabled
    
    offset = case @strategy
    when :gaussian
      EntropySources.gaussian(stddev: @intensity * 6)
    when :levy
      EntropySources.levy(scale: @intensity * 12)
    when :brownian
      @walker ||= EntropySources::DrunkWalk.new(step_size: @intensity * 0.5)
      @walker.next_value * 12
    when :chaotic
      @chaos ||= EntropySources::LorenzAttractor.new
      @chaos.next_value * @intensity * 24
    when :multi
      blend_strategies(pitch)
    end
    
    result = pitch + offset
    result += (rand > 0.5 ? 12 : -12) if @octave_displacement && rand < @intensity * 0.2
    result = (result * 4).round / 4.0 if @microtonal  # Quarter-tones
    result.round.clamp(24, 96)
  end
end
```

### Duration Derangement

```ruby
class DurationDerangement
  def initialize(
    enabled: true,
    intensity: 0.5,
    strategy: :gaussian,
    min_duration: 0.01,
    allow_extreme: false
  )
    @enabled = enabled
    @intensity = intensity
    @strategy = strategy
    @min_duration = min_duration
    @allow_extreme = allow_extreme
  end
  
  def derange(duration)
    return duration unless @enabled
    
    factor = case @strategy
    when :gaussian
      1.0 + EntropySources.gaussian(stddev: @intensity * 0.5)
    when :exponential
      Math.exp(EntropySources.gaussian(stddev: @intensity))
    when :chaotic
      @chaos ||= EntropySources::HenonMap.new
      0.5 + @chaos.next_value.abs * 1.5
    end
    
    result = duration * factor
    result = result.clamp(@min_duration, 10.0) unless @allow_extreme
    result
  end
end
```

### Onset Derangement

```ruby
class OnsetDerangement
  def initialize(
    enabled: true,
    intensity: 0.3,
    allow_negative: false,
    swing_amount: 0
  )
    @enabled = enabled
    @intensity = intensity
    @allow_negative = allow_negative
    @swing_amount = swing_amount
  end
  
  def derange(onset, event_index: 0)
    return onset unless @enabled
    
    offset = EntropySources.gaussian(stddev: @intensity * 0.2)
    
    # Apply swing
    if @swing_amount > 0 && event_index.odd?
      offset += @swing_amount
    end
    
    result = onset + offset
    result = [result, 0].max unless @allow_negative
    result
  end
end
```

### Structure Derangement

```ruby
class StructureDerangement
  def initialize(
    enabled: true,
    swap_probability: 0.1,
    reverse_probability: 0.05,
    skip_probability: 0.05,
    repeat_probability: 0.1
  )
    @enabled = enabled
    @swap_probability = swap_probability
    @reverse_probability = reverse_probability
    @skip_probability = skip_probability
    @repeat_probability = repeat_probability
  end
  
  def derange_sequence(events)
    return events unless @enabled
    
    result = events.dup
    
    # Random swaps
    if rand < @swap_probability && result.length >= 2
      i, j = rand(result.length), rand(result.length)
      result[i], result[j] = result[j], result[i]
    end
    
    # Reverse segments
    if rand < @reverse_probability && result.length >= 3
      start = rand(result.length - 2)
      len = rand(2..[result.length - start, 4].min)
      result[start, len] = result[start, len].reverse
    end
    
    # Skip events
    result = result.reject { rand < @skip_probability }
    
    # Repeat events
    result = result.flat_map { |e| rand < @repeat_probability ? [e, e] : [e] }
    
    result
  end
end
```

### Meta Derangement

The derangement parameters themselves evolve:

```ruby
class MetaDerangement
  def initialize(
    enabled: true,
    intensity_drift: 0.1,
    strategy_mutation: false,
    self_modification: false
  )
    @enabled = enabled
    @intensity_drift = intensity_drift
    @strategy_mutation = strategy_mutation
    @self_modification = self_modification
  end
  
  def evolve(config)
    return config unless @enabled
    
    # Drift intensities
    [:pitch, :duration, :amplitude, :onset].each do |param|
      derangement = config.send(param)
      drift = EntropySources.gaussian(stddev: @intensity_drift)
      derangement.intensity = (derangement.intensity + drift).clamp(0, 1)
    end
    
    # Mutate strategies
    if @strategy_mutation && rand < 0.1
      strategies = [:gaussian, :levy, :brownian, :chaotic]
      config.pitch.strategy = strategies.sample
    end
    
    config
  end
end
```

## Preset Configurations

### Subtle

```ruby
def self.subtle
  new(
    pitch: PitchDerangement.new(enabled: true, intensity: 0.1),
    duration: DurationDerangement.new(enabled: true, intensity: 0.1),
    amplitude: AmplitudeDerangement.new(enabled: true, intensity: 0.1),
    onset: OnsetDerangement.new(enabled: false),
    structure: StructureDerangement.new(enabled: false),
    meta: MetaDerangement.new(enabled: false)
  )
end
```

### Moderate

```ruby
def self.moderate
  new(
    pitch: PitchDerangement.new(enabled: true, intensity: 0.3, strategy: :gaussian),
    duration: DurationDerangement.new(enabled: true, intensity: 0.3),
    amplitude: AmplitudeDerangement.new(enabled: true, intensity: 0.3),
    onset: OnsetDerangement.new(enabled: true, intensity: 0.2),
    structure: StructureDerangement.new(enabled: true, swap_probability: 0.1),
    meta: MetaDerangement.new(enabled: false)
  )
end
```

### Chaotic

```ruby
def self.chaotic
  new(
    pitch: PitchDerangement.new(enabled: true, intensity: 0.6, strategy: :levy),
    duration: DurationDerangement.new(enabled: true, intensity: 0.5, strategy: :chaotic),
    amplitude: AmplitudeDerangement.new(enabled: true, intensity: 0.5),
    onset: OnsetDerangement.new(enabled: true, intensity: 0.4),
    structure: StructureDerangement.new(enabled: true, swap_probability: 0.3, reverse_probability: 0.1),
    meta: MetaDerangement.new(enabled: true, intensity_drift: 0.1)
  )
end
```

### Maximum

```ruby
def self.maximum
  new(
    pitch: PitchDerangement.new(
      enabled: true, intensity: 1.0, strategy: :multi,
      strategies: [:gaussian, :levy, :chaotic, :brownian],
      microtonal: true, octave_displacement: true
    ),
    duration: DurationDerangement.new(
      enabled: true, intensity: 1.0, strategy: :multi,
      allow_extreme: true
    ),
    amplitude: AmplitudeDerangement.new(
      enabled: true, intensity: 1.0,
      allow_silence: true
    ),
    onset: OnsetDerangement.new(
      enabled: true, intensity: 1.0,
      allow_negative: true, allow_overlap: true
    ),
    structure: StructureDerangement.new(
      enabled: true, swap_probability: 0.5,
      reverse_probability: 0.2, skip_probability: 0.1,
      repeat_probability: 0.15
    ),
    meta: MetaDerangement.new(
      enabled: true, intensity_drift: 0.3,
      strategy_mutation: true, self_modification: true
    )
  )
end
```

## Deranging Interpreter

Wraps standard interpretation with perturbation:

```ruby
class DerangingInterpreter
  attr_reader :events, :stats
  
  def initialize(config)
    @config = config
    @events = []
    @stats = { total: 0, pitch_changes: 0, duration_changes: 0 }
  end
  
  def interpret(pattern, matter)
    # First, potentially derange structure
    if pattern.is_a?(FreeMonad::Suspend) && 
       pattern.instruction.is_a?(FreeMonad::Sequence)
      deranged_actions = @config.structure.derange_sequence(pattern.instruction.actions)
      pattern = FreeMonad::Suspend.new(FreeMonad::Sequence.new(deranged_actions))
    end
    
    interpret_inner(pattern, matter, 0)
    
    # Evolve meta-parameters
    @config = @config.meta.evolve(@config) if @config.meta.enabled
    
    @events
  end
  
  private
  
  def interpret_inner(pattern, matter, beat)
    return beat if pattern.pure?
    
    case pattern.instruction
    when FreeMonad::PlayNote
      emit_note(pattern.instruction, matter, beat)
    when FreeMonad::PlayChord
      emit_chord(pattern.instruction, matter, beat)
    when FreeMonad::Rest
      emit_rest(pattern.instruction, matter, beat)
    when FreeMonad::Sequence
      # ...recursive interpretation
    end
  end
  
  def emit_note(instruction, matter, beat)
    @stats[:total] += 1
    
    orig_pitch = instruction.pitch
    orig_dur = instruction.duration
    orig_amp = instruction.amplitude
    
    # Derange everything
    deranged_pitch = @config.pitch.derange(orig_pitch)
    deranged_dur = @config.duration.derange(orig_dur)
    deranged_amp = @config.amplitude.derange(orig_amp)
    deranged_onset = @config.onset.derange(beat, event_index: @stats[:total])
    
    # Track stats
    @stats[:pitch_changes] += 1 if (deranged_pitch - orig_pitch).abs > 0.5
    @stats[:duration_changes] += 1 if (deranged_dur - orig_dur).abs > 0.05
    
    @events << {
      type: :note,
      at: deranged_onset,
      dur: deranged_dur,
      pitch: deranged_pitch,
      amplitude: deranged_amp,
      original: { pitch: orig_pitch, dur: orig_dur, amp: orig_amp }
    }
    
    beat + deranged_dur
  end
end
```

## Usage

### Command Line

```bash
# Progressive chaos demonstration
just max-dynamism

# Artist-specific maximum dynamism
just max-aphex      # Lévy flights + chaotic durations
just max-autechre   # Brownian pitch + irrational time

# Compare chaos levels
just chaos-spectrum
```

### Ruby API

```ruby
require_relative 'lib/maximum_dynamism'

# Create custom configuration
config = MaximumDynamism::DerangementConfig.new(
  pitch: MaximumDynamism::PitchDerangement.new(
    enabled: true,
    intensity: 0.7,
    strategy: :levy,
    microtonal: true
  )
)

# Derange any pattern
base_pattern = QuantumAphexAutechre::AphexTwinPatterns.drill_n_bass(duration: 8.0)
result = MaximumDynamism::PatternDerangers.derange(base_pattern, config: config)

# Access results
events = result[:events]
stats = result[:stats]
puts "Generated #{events.length} events"
puts "#{stats[:pitch_changes]} pitch changes"
```

### Artist Presets

```ruby
# Aphex Twin configuration
aphex_config = MaximumDynamism::PatternDerangers.aphex_config
# - Lévy flights for sudden pitch jumps
# - Exponential duration scaling
# - Spiky amplitude dynamics
# - Structural repetition

# Autechre configuration
autechre_config = MaximumDynamism::PatternDerangers.autechre_config
# - Brownian pitch drift
# - Chaotic duration (no quantization)
# - Smooth amplitude
# - Overlap allowed
```

## Visualization

The derangement system tracks statistics for analysis:

```ruby
result = derange(pattern)

puts "Statistics:"
puts "  Total events: #{result[:stats][:total]}"
puts "  Pitch changes: #{result[:stats][:pitch_changes]}"
puts "  Duration changes: #{result[:stats][:duration_changes]}"

# Events retain original values for comparison
result[:events].each do |event|
  orig = event[:original]
  puts "Pitch: #{orig[:pitch]} → #{event[:pitch]} (Δ#{event[:pitch] - orig[:pitch]})"
end
```

## Mathematical Foundation

The derangement operation can be viewed categorically as:

```
D : Pattern × Entropy → Pattern
```

Where:
- `Pattern` is the Free Monad over musical instructions
- `Entropy` is the comonad of random sources
- `D` applies point-wise perturbation while preserving structure

The module action becomes:

```
(Pattern × Entropy) ⊗ Matter → ScoreEvents
```

Derangement commutes with interpretation up to the entropy's influence on timing.
