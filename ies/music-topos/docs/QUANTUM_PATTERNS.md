# Quantum Patterns: Aphex Twin & Autechre

**Categorical Derivation of Generative Electronic Music**

This document describes the implementation of Aphex Twin and Autechre-inspired patterns using the Free Monad / Cofree Comonad architecture.

## Theoretical Foundations

Both artists work with **nested temporal structures** and **probability-weighted decision trees** — exactly what Free/Cofree captures.

### Aphex Twin: Superposition of Metric Grids

- 4/4 pulse coexists with 7/8, 5/4, 11/8
- "Drill 'n' bass" = high-frequency sampling of breakbeat space
- Equation-derived melodies (Windowlicker formula speculation)
- The "creepy" quality = microtonal beating + uncanny valley timing

### Autechre: Generative Grammar

- Markov chains over rhythmic cells
- Cellular automata for parameter evolution
- Max/MSP → categorical: objects = states, morphisms = transitions
- "Anti-groove" = rhythms in superposition that never fully collapse

## Module Action

```
Pattern (Free F) = Decision tree of possible musical events
Matter (Cofree G) = Environment providing:
  - Current metric position (polyrhythmic phase)
  - Probability distributions for next events
  - Accumulated history (for Markov transitions)
  - Cellular automaton state
```

At each node, Matter "answers" Pattern's "question" by:
1. Selecting from superposed options based on current state
2. Applying probability weights from accumulated context
3. Evolving internal state (CA step, Markov transition)

## Rhythmic Category

### Polymetric Grid

Multiple metric grids running simultaneously:

```ruby
class PolymetricGrid
  attr_reader :periods, :accents
  
  def initialize(*periods, accents: nil)
    @periods = periods
    @accents = accents || periods.map { |p| [0] }
  end
  
  # Get the phase vector at time t
  def phase_at(t)
    @periods.map { |p| t % p }
  end
  
  # Interference pattern: how many grids align?
  def alignment_at(t)
    phase = phase_at(t)
    phase.each_with_index.count { |p, i| @accents[i].include?(p) }
  end
  
  # Full cycle length = LCM(periods)
  def period
    @periods.reduce(1) { |lcm, p| lcm.lcm(p) }
  end
end
```

**Usage:**

```ruby
# Aphex-style 4+5+7 polymetric grid
grid = RhythmCategory::PolymetricGrid.new(4, 5, 7)

# Find alignment points
(0..grid.period).each do |t|
  alignment = grid.alignment_at(t)
  puts "Beat #{t}: #{alignment} grids align" if alignment > 1
end
```

### Euclidean Rhythms

Optimal distribution of k onsets in n positions (Toussaint algorithm):

```ruby
def self.euclidean(k, n, rotation: 0)
  return Array.new(n, false) if k.zero?
  return Array.new(n, true) if k >= n
  
  pattern = Array.new(n, false)
  step = n.to_f / k
  k.times { |i| pattern[((i * step) % n).floor] = true }
  pattern.rotate(rotation)
end
```

**Examples:**

| Pattern | Traditional Name |
|---------|------------------|
| `euclidean(3, 8)` | Cuban tresillo |
| `euclidean(5, 8)` | Cuban cinquillo |
| `euclidean(5, 12)` | Bembé |
| `euclidean(7, 16)` | Samba |

### Irrational Meters

Durations based on mathematical constants:

```ruby
IRRATIONAL_RATIOS = {
  phi: (1 + Math.sqrt(5)) / 2,        # Golden ratio ≈ 1.618
  sqrt2: Math.sqrt(2),                 # √2 ≈ 1.414
  pi_4: Math::PI / 4,                  # π/4 ≈ 0.785
  e_3: Math::E / 3                     # e/3 ≈ 0.906
}

def self.irrational_duration(base_duration, ratio_name)
  base_duration * IRRATIONAL_RATIOS[ratio_name]
end
```

## Pitch Category

### Equation-Derived Melodies

The Windowlicker/ΔMi−1 spectrograms suggest mathematical functions:

```ruby
class EquationMelody
  def initialize(fn, sample_rate: 16, quantize: :chromatic)
    @fn = fn
    @sample_rate = sample_rate
    @quantize = quantize
  end
  
  def generate(duration)
    samples = (duration * @sample_rate).to_i
    (0...samples).map do |i|
      t = i.to_f / @sample_rate
      raw_pitch = @fn.call(t)
      quantize_pitch(raw_pitch)
    end
  end
end
```

**Equation Types:**

```ruby
APHEX_EQUATIONS = {
  # Logarithmic spiral in pitch space
  spiral: ->(t) { 60 + 12 * Math.log(1 + t) * Math.sin(t * Math::PI) },
  
  # Face-like spectrogram approximation
  face: ->(t) { 60 + 24 * Math.sin(t * 0.5) * Math.exp(-t * 0.1) },
  
  # Logistic map for deterministic chaos
  logistic: ->(t, r: 3.7, x: 0.5) {
    x_next = x
    (t * 10).to_i.times { x_next = r * x_next * (1 - x_next) }
    36 + 48 * x_next
  },
  
  # Modular arithmetic patterns
  modular: ->(t, m: 7, b: 60) { b + ((t * 12).to_i % m) * 12 / m }
}
```

### Pitch Drift

Random walk for Autechre-style gradual detuning:

```ruby
class PitchDrift
  def initialize(center, max_deviation: 0.5, step_size: 0.05)
    @center = center
    @max_deviation = max_deviation
    @step_size = step_size
    @current_offset = 0
  end
  
  def next_pitch
    @current_offset += (rand - 0.5) * @step_size * 2
    @current_offset = @current_offset.clamp(-@max_deviation, @max_deviation)
    @center + @current_offset
  end
end
```

## Stochastic Systems

### Markov Chains

Higher-order Markov chains over rhythmic cells:

```ruby
class MarkovChain
  attr_reader :states, :transitions, :current_state
  
  def initialize(states, transitions)
    @states = states
    @transitions = transitions  # Hash: state => [[next_state, probability], ...]
    @current_state = states.sample
  end
  
  def step
    probs = @transitions[@current_state] || []
    return @current_state if probs.empty?
    
    r = rand
    cumulative = 0
    probs.each do |next_state, prob|
      cumulative += prob
      if r <= cumulative
        @current_state = next_state
        return @current_state
      end
    end
    
    @current_state
  end
end
```

**Higher-Order:**

```ruby
class HigherOrderMarkov
  def initialize(order, transitions)
    @order = order
    @transitions = transitions
    @history = []
  end
  
  def step
    context = @history.last(@order)
    probs = @transitions[context] || {}
    
    # Sample from distribution
    next_state = weighted_sample(probs)
    @history << next_state
    next_state
  end
end
```

### Cellular Automata

Elementary CA for rhythm generation:

```ruby
class ElementaryCA
  RULES = (0..255).map do |n|
    n.to_s(2).rjust(8, '0').chars.map(&:to_i).reverse
  end
  
  def initialize(size, rule: 110, init: nil)
    @size = size
    @rule = RULES[rule]
    @state = init || random_init
  end
  
  def step
    new_state = Array.new(@size)
    @size.times do |i|
      left = @state[(i - 1) % @size]
      center = @state[i]
      right = @state[(i + 1) % @size]
      pattern = left * 4 + center * 2 + right
      new_state[i] = @rule[pattern]
    end
    @state = new_state
  end
  
  def to_rhythm
    @state
  end
  
  def to_pitches(base: 36, step: 2)
    @state.each_with_index
          .select { |v, _| v == 1 }
          .map { |_, i| base + i * step }
  end
end
```

### Game of Life

2D CA for texture generation:

```ruby
class GameOfLife
  def initialize(width, height, density: 0.3)
    @width = width
    @height = height
    @grid = random_init(density)
  end
  
  def step
    new_grid = Array.new(@height) { Array.new(@width, 0) }
    
    @height.times do |y|
      @width.times do |x|
        neighbors = count_neighbors(x, y)
        alive = @grid[y][x] == 1
        
        new_grid[y][x] = if alive
          (neighbors == 2 || neighbors == 3) ? 1 : 0
        else
          neighbors == 3 ? 1 : 0
        end
      end
    end
    
    @grid = new_grid
  end
  
  def to_pitches(base: 36, x_step: 2, y_step: 12)
    pitches = []
    @height.times do |y|
      @width.times do |x|
        if @grid[y][x] == 1
          pitches << base + x * x_step + y * y_step
        end
      end
    end
    pitches
  end
end
```

## Quantum Patterns

### Superposition

Weighted collection of alternatives that collapse on measurement:

```ruby
class Superposition
  def initialize(options_with_weights)
    @options = options_with_weights  # [[value, probability], ...]
    normalize!
  end
  
  def measure
    r = rand
    cumulative = 0
    @options.each do |value, prob|
      cumulative += prob
      return value if r <= cumulative
    end
    @options.last[0]
  end
  
  private
  
  def normalize!
    total = @options.sum { |_, prob| prob }
    @options.map! { |v, p| [v, p / total] }
  end
end
```

### Entangled Pairs

Parameters whose distributions change based on measurement of the other:

```ruby
class EntangledPair
  def initialize(a_options, b_options, correlation_matrix)
    @a_options = a_options
    @b_options = b_options
    @correlation = correlation_matrix
  end
  
  def measure
    # Measure A first
    a_value = weighted_sample(@a_options)
    a_index = @a_options.find_index { |v, _| v == a_value }
    
    # B's distribution depends on A's outcome
    b_probs = @correlation[a_index]
    b_value = weighted_sample(@b_options.zip(b_probs).map { |(v, _), p| [v, p] })
    
    [a_value, b_value]
  end
end
```

## Aphex Twin Patterns

### Drill 'n' Bass

Hyper-fast fragmentation with gaps:

```ruby
def self.drill_n_bass(duration: 8.0, intensity: 0.7)
  events = []
  time = 0
  base_pitch = 36
  
  while time < duration
    # Random duration from distribution weighted by intensity
    dur = 0.02 + rand * (0.15 - intensity * 0.1)
    
    # Probability of playing vs gap
    if rand < (0.6 + intensity * 0.3)
      pitch = base_pitch + rand(-12..24)
      amp = 0.2 + rand * 0.3
      events << play_note!(pitch, dur, amp)
    else
      events << rest!(dur * (1 + rand))
    end
    
    time += dur
  end
  
  sequence!(*events)
end
```

### Ambient Drift

Slow modulation with microtonal beating:

```ruby
def self.ambient_drift(base: 48, duration: 32.0)
  events = []
  
  # Foundation chord with slight detuning
  chord = [base, base + 0.1, base + 7, base + 7.05]
  events << play_chord!(chord.map(&:round), duration, 0.2)
  
  # Slow melody with microtonal inflections
  drift = PitchDrift.new(base + 12, max_deviation: 0.3, step_size: 0.02)
  
  (duration / 4).to_i.times do
    pitch = drift.next_pitch
    events << play_note!(pitch.round, 3.0, 0.15)
    events << rest!(1.0)
  end
  
  parallel!(*events)
end
```

### Equation Melody

Using spiral equation:

```ruby
def self.equation_melody(base: 48, duration: 8.0)
  eq = EquationMelody.new(APHEX_EQUATIONS[:spiral], quantize: :chromatic)
  pitches = eq.generate(duration)
  
  events = pitches.map do |p|
    play_note!(p.clamp(24, 96), 0.2, 0.25)
  end
  
  sequence!(*events)
end
```

## Autechre Patterns

### Generative Rhythm

Markov chain over rhythmic cells:

```ruby
def self.generative_rhythm(duration: 16.0, order: 2)
  # Define rhythmic cells
  cells = {
    a: [0.25, 0.25, 0.5],           # Straight
    b: [0.33, 0.33, 0.34],          # Triplet
    c: [0.125, 0.125, 0.25, 0.5],   # Syncopated
    d: [0.5, 0.25, 0.125, 0.125],   # Reverse syncopation
  }
  
  # Transition matrix
  transitions = {
    [:a, :a] => { a: 0.2, b: 0.4, c: 0.3, d: 0.1 },
    [:a, :b] => { a: 0.3, b: 0.2, c: 0.3, d: 0.2 },
    # ... etc
  }
  
  markov = HigherOrderMarkov.new(order, transitions)
  events = []
  time = 0
  
  while time < duration
    cell = markov.step
    durations = cells[cell]
    
    durations.each do |dur|
      pitch = 36 + rand(24)
      events << play_note!(pitch, dur, 0.3)
      time += dur
    end
  end
  
  sequence!(*events)
end
```

### Cellular Rhythm

Driven by Rule 110:

```ruby
def self.cellular_rhythm(rule: 110, steps: 32)
  ca = CellularAutomata::ElementaryCA.new(16, rule: rule)
  events = []
  
  steps.times do |step|
    rhythm = ca.to_rhythm
    pitches = ca.to_pitches(base: 36, step: 2)
    
    rhythm.each_with_index do |active, i|
      if active == 1
        pitch = pitches.include?(36 + i * 2) ? 36 + i * 2 : 48
        dur = 0.05 + (step * 0.005)
        amp = 0.15 + (i * 0.02)
        events << play_note!(pitch, dur, amp)
      end
    end
    
    events << rest!(0.2)
    ca.step
  end
  
  sequence!(*events)
end
```

### Anti-Groove

Rhythms that resist quantization:

```ruby
def self.anti_groove(duration: 8.0)
  events = []
  time = 0
  base_pitches = [36, 41, 46, 48, 53]
  
  while time < duration
    # Use irrational ratios for duration
    ratio = IRRATIONAL_RATIOS.values.sample
    dur = (0.1 * ratio).clamp(0.03, 0.5)
    
    pitch = base_pitches.sample
    drift = PitchDrift.new(pitch, max_deviation: 2, step_size: 0.3)
    actual_pitch = drift.next_pitch.round
    
    amp = 0.2 + rand * 0.2
    events << play_note!(actual_pitch, dur, amp)
    
    # Rest with irrational duration
    rest_ratio = IRRATIONAL_RATIOS.values.sample
    rest_dur = 0.05 * rest_ratio
    events << rest!(rest_dur) if rest_dur > 0.01
    
    time += dur + rest_dur
  end
  
  sequence!(*events)
end
```

## Usage

### Command Line

```bash
# Full Aphex showcase
just aphex

# Full Autechre showcase
just autechre

# Combined collision
just quantum-electronic

# Individual patterns
just aphex-drill     # Fast drill 'n' bass
just aphex-ambient   # Slow ambient drift
just autechre-generative  # Markov rhythm
just autechre-cellular    # Rule 110 CA
```

### Ruby API

```ruby
require_relative 'lib/quantum_aphex_autechre'

# Build individual patterns
drill = QuantumAphexAutechre::AphexTwinPatterns.drill_n_bass(duration: 8.0)
ca = QuantumAphexAutechre::AutechrePatterns.cellular_rhythm(rule: 110)

# Full showcases
aphex = QuantumAphexAutechre::Showcase.aphex_showcase
autechre = QuantumAphexAutechre::Showcase.autechre_showcase
collision = QuantumAphexAutechre::Showcase.quantum_electronic_showcase
```

## References

- **Aphex Twin**: _Selected Ambient Works 85-92_, _Richard D. James Album_, _Drukqs_
- **Autechre**: _Tri Repetae_, _Confield_, _Exai_
- **Toussaint, G.**: "The Euclidean Algorithm Generates Traditional Musical Rhythms"
- **Wolfram, S.**: _A New Kind of Science_ (cellular automata)
