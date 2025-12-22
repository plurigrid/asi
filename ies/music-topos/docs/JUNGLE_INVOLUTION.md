# Industrial Jungle Self-Involution

**ι: UIState → UIState where ι∘ι → id (Fixed Point)**

This document describes the self-involution system for generating industrial jungle/drum and bass through evolutionary optimization.

## Philosophy

The system models jungle production as an **involution** — a function that, when applied twice, approaches identity (a fixed point):

```
ι : UIState → UIState
ι ∘ ι → id
```

Starting from chaotic breakbeats, the system evolves toward a stable "groove" through:
1. **Trifurcation**: Generate three candidate variations
2. **Evaluation**: Score candidates on musical criteria
3. **Selection**: Keep the best (argmax)
4. **Iteration**: Repeat until fixed point

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        SELF-INVOLUTION ENGINE                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  UIState_n ──────► TRIFURCATE ──────► [EXPAND, MUTATE, TRANSPOSE]          │
│                         │                                                   │
│                         ▼                                                   │
│                    EVALUATE each                                            │
│                         │                                                   │
│                         ▼                                                   │
│                    ARGMAX select                                            │
│                         │                                                   │
│                         ▼                                                   │
│                    UIState_{n+1}                                            │
│                         │                                                   │
│                         ▼                                                   │
│                  ι∘ι = id? ─────► Yes ─────► Fixed Point (done)            │
│                         │                                                   │
│                        No                                                   │
│                         │                                                   │
│                         └─────────────────────────────────────────► (loop)  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Non-Standard Tempo

Jungle operates on **tempo fields**, not tempo values:

### Standard Tempo is Wrong

- Base tempo: 160-180 BPM
- Half-time feel on bass: 80-90 BPM polyrhythm
- Breakbeat subdivisions: 32nd notes, triplets, quintuplets **simultaneously**
- Tempo drift: ±5% continuous modulation
- Time-stretching artifacts: pitch-independent tempo warping

**The beat is NEVER on the grid. The grid is a lie.**

### TempoField Implementation

```ruby
class TempoField
  attr_reader :base_bpm, :current_bpm, :phase, :drift_rate
  
  def initialize(base_bpm: 172, drift_rate: 0.03)
    @base_bpm = base_bpm
    @current_bpm = base_bpm
    @drift_rate = drift_rate
    @phase = 0
    @chaos = EntropySources::LorenzAttractor.new
    @drunk = EntropySources::DrunkWalk.new(step_size: 0.02, bounds: [-0.08, 0.08])
  end
  
  def tick
    # Tempo is a FIELD, not a value
    # Lorenz attractor for macro drift
    chaos_mod = @chaos.next_value * @drift_rate
    
    # Drunk walk for micro-timing
    micro_drift = @drunk.next_value * 0.02
    
    # Sinusoidal "breathing"
    @phase += 0.01
    breath = Math.sin(@phase * 0.3) * 0.015
    
    @current_bpm = @base_bpm * (1 + chaos_mod + micro_drift + breath)
    @current_bpm.clamp(@base_bpm * 0.85, @base_bpm * 1.15)
  end
  
  def beat_duration
    60.0 / @current_bpm
  end
  
  # Polyrhythmic subdivisions
  def subdivisions
    {
      straight: 1.0,
      double: 0.5,
      triple: 1.0 / 3,
      quad: 0.25,
      quint: 0.2,
      sept: 1.0 / 7,
      phi: 1.0 / ((1 + Math.sqrt(5)) / 2),  # Golden ratio
      sqrt2: 1.0 / Math.sqrt(2)
    }
  end
  
  def random_subdivision
    subdivisions.values.sample * beat_duration
  end
end
```

## Breakbeat Engine

The Amen break is a **seed**, not a template:

```ruby
class BreakbeatEngine
  KICK = 36
  SNARE = 38
  CLOSED_HAT = 42
  OPEN_HAT = 46
  
  # Amen break pattern (will be destroyed)
  AMEN_SEED = [
    [:kick, 0],    [:hat, 0.25],  [:snare, 0.5], [:hat, 0.75],
    [:kick, 1.0],  [:hat, 1.25],  [:snare, 1.5], [:kick, 1.75],
    [:kick, 2.0],  [:hat, 2.25],  [:snare, 2.5], [:hat, 2.5],
    [:kick, 2.75], [:hat, 3.0],   [:snare, 3.5], [:hat, 3.75]
  ]
  
  def initialize(tempo_field)
    @tempo = tempo_field
    @current_pattern = AMEN_SEED.dup
    @chop_probability = 0.4
    @stutter_probability = 0.3
    @reverse_probability = 0.15
    @time_stretch_range = 0.5..2.0
  end
  
  def generate_bar
    events = []
    pattern = mangle_pattern(@current_pattern)
    
    pattern.each do |hit_type, time|
      @tempo.tick
      
      # Time stretch the hit position
      stretched_time = time * rand(@time_stretch_range)
      
      # Quantize to subdivision (or don't)
      if rand > 0.3
        subdiv = @tempo.random_subdivision
        stretched_time = (stretched_time / subdiv).round * subdiv
      end
      
      pitch, amp, dur = hit_params(hit_type)
      
      # Stutter
      if rand < @stutter_probability
        stutters = rand(2..6)
        stutter_dur = dur / stutters
        stutters.times do |i|
          events << {
            time: stretched_time + i * stutter_dur * 0.7,
            pitch: pitch + (rand > 0.5 ? rand(-3..3) : 0),
            amp: amp * (1 - i * 0.12),
            dur: stutter_dur * 0.8
          }
        end
      else
        events << { time: stretched_time, pitch: pitch, amp: amp, dur: dur }
      end
    end
    
    # Add ghost notes
    rand(3..8).times do
      events << {
        time: rand * 4.0,
        pitch: [CLOSED_HAT, SNARE, TOM_MID].sample,
        amp: 0.05 + rand * 0.1,
        dur: 0.02 + rand * 0.05
      }
    end
    
    events.sort_by { |e| e[:time] }
  end
  
  private
  
  def mangle_pattern(pattern)
    result = pattern.dup
    
    # Chop: remove random hits
    result = result.select { rand > @chop_probability * 0.5 }
    
    # Shuffle segments
    if rand < 0.3
      segment_size = rand(2..4)
      result = result.each_slice(segment_size).to_a.shuffle.flatten(1)
    end
    
    # Reverse segments
    if rand < @reverse_probability && result.length > 2
      start = rand(result.length - 1)
      len = rand(2..[result.length - start, 4].min)
      result[start, len] = result[start, len].reverse
    end
    
    # Time warp
    result.map do |type, time|
      warp = 1.0 + (rand - 0.5) * 0.3
      [type, time * warp]
    end
  end
end
```

## Bass Engine

Half-time Reese bass with beating detuning:

```ruby
class BassEngine
  def initialize(tempo_field)
    @tempo = tempo_field
    @root = 36  # Low C
    @current_note = @root
    @movement_probability = 0.4
    @intervals = [-5, -3, 0, 2, 4, 7, 12]  # Dark intervals
  end
  
  def generate_bar
    events = []
    
    # Bass moves at half-time (2 beats = 1 bass hit)
    2.times do |half|
      # Slight detuning for beating
      detune = (rand - 0.5) * 0.3
      pitches = [@current_note, @current_note + detune]
      
      events << {
        time: half * 2.0,
        pitches: pitches,
        amp: 0.5 + rand * 0.1,
        dur: 1.8,
        type: :bass
      }
      
      # Move to next note?
      if rand < @movement_probability
        @current_note += @intervals.sample
        @current_note = @current_note.clamp(24, 48)
      end
    end
    
    events
  end
end
```

## UIState

The state being evolved:

```ruby
class UIState
  attr_accessor :break_pattern, :bass_pattern, :tempo_offset, :intensity
  
  def initialize(break_pattern: [], bass_pattern: [], tempo_offset: 0, intensity: 0.5)
    @break_pattern = break_pattern
    @bass_pattern = bass_pattern
    @tempo_offset = tempo_offset
    @intensity = intensity
  end
  
  def to_events
    all_events = []
    
    @break_pattern.each do |e|
      all_events << {
        type: :drum,
        at: e[:time],
        pitch: e[:pitch],
        dur: e[:dur],
        amplitude: e[:amp]
      }
    end
    
    @bass_pattern.each do |e|
      all_events << {
        type: :bass,
        at: e[:time],
        pitches: e[:pitches],
        dur: e[:dur],
        amplitude: e[:amp]
      }
    end
    
    all_events.sort_by { |e| e[:at] }
  end
end
```

## Trifurcation

Three candidate operations:

### Expand

Increase density and complexity:

```ruby
def self.expand(state)
  new_breaks = state.break_pattern.flat_map do |event|
    if rand < 0.3
      # Split into two events
      [
        event.merge(dur: event[:dur] * 0.5, amp: event[:amp] * 0.9),
        event.merge(time: event[:time] + event[:dur] * 0.5, dur: event[:dur] * 0.5)
      ]
    else
      [event]
    end
  end
  
  # Add new ghost notes
  2.times do
    new_breaks << {
      time: rand * 4.0,
      pitch: [42, 38, 45].sample,
      amp: 0.08 + rand * 0.07,
      dur: 0.03
    }
  end
  
  UIState.new(
    break_pattern: new_breaks,
    bass_pattern: state.bass_pattern,
    intensity: [state.intensity + 0.1, 1.0].min
  )
end
```

### Mutate

Random parameter changes:

```ruby
def self.mutate(state)
  mutated_breaks = state.break_pattern.map do |event|
    e = event.dup
    
    # Pitch mutation
    e[:pitch] += rand(-3..3) if rand < 0.2
    
    # Timing mutation
    e[:time] += (rand - 0.5) * 0.1 if rand < 0.3
    
    # Amplitude mutation
    e[:amp] *= (0.8 + rand * 0.4) if rand < 0.25
    
    e
  end
  
  UIState.new(
    break_pattern: mutated_breaks,
    bass_pattern: state.bass_pattern.map { |e|
      if rand < 0.15
        e.merge(pitches: e[:pitches].map { |p| p + [-5, 0, 7, 12].sample })
      else
        e
      end
    }
  )
end
```

### Transpose

Shift pitch/time domains:

```ruby
def self.transpose(state)
  pitch_shift = [-12, -5, 0, 5, 7, 12].sample
  time_shift = (rand - 0.5) * 0.2
  
  UIState.new(
    break_pattern: state.break_pattern.map { |e|
      e.merge(
        pitch: e[:pitch] + pitch_shift,
        time: e[:time] + time_shift
      )
    },
    bass_pattern: state.bass_pattern.map { |e|
      e.merge(pitches: e[:pitches].map { |p| (p + pitch_shift).clamp(24, 60) })
    }
  )
end
```

## Evaluation

Multi-criteria scoring:

```ruby
class Evaluator
  def evaluate(state)
    scores = {
      density: density_score(state),
      syncopation: syncopation_score(state),
      bass_power: bass_power_score(state),
      chaos: chaos_score(state),
      novelty: novelty_score(state)
    }
    
    # Weighted combination
    weights = { density: 0.2, syncopation: 0.25, bass_power: 0.2, chaos: 0.15, novelty: 0.2 }
    total = weights.sum { |k, w| scores[k] * w }
    
    scores.merge(total: total)
  end
  
  private
  
  def density_score(state)
    # Optimal density: 15-30 events per bar
    count = state.break_pattern.length
    return 0 if count < 5
    return 1.0 if count.between?(15, 30)
    count > 30 ? 0.7 : count / 15.0
  end
  
  def syncopation_score(state)
    # Reward off-grid events
    times = state.break_pattern.map { |e| e[:time] }
    off_grid = times.count { |t| (t * 4) % 1 > 0.1 && (t * 4) % 1 < 0.9 }
    (off_grid.to_f / [times.length, 1].max).clamp(0, 1)
  end
  
  def bass_power_score(state)
    # Bass should be present and weighty
    return 0 if state.bass_pattern.empty?
    avg_amp = state.bass_pattern.map { |e| e[:amp] }.sum / state.bass_pattern.length
    avg_amp.clamp(0, 1)
  end
  
  def chaos_score(state)
    # Some variance is good, too much is bad
    times = state.break_pattern.map { |e| e[:time] }
    return 0 if times.length < 3
    
    intervals = times.each_cons(2).map { |a, b| b - a }
    variance = intervals.map { |i| (i - intervals.sum / intervals.length) ** 2 }.sum / intervals.length
    
    # Optimal variance around 0.1
    1.0 - (variance - 0.1).abs.clamp(0, 1)
  end
  
  def novelty_score(state)
    # Compare to patterns in intuition bank
    patterns = PatternRecognizer.extract_patterns(state)
    familiarity = patterns.map { |p| @intuition_bank.familiarity(p) }.sum / [patterns.length, 1].max
    1.0 - familiarity  # Novelty = inverse of familiarity
  end
end
```

## Intuition Bank

Pattern memory with decay:

```ruby
class IntuitionBank
  def initialize(decay_rate: 0.95)
    @patterns = {}  # pattern_hash => { count:, success_rate:, last_seen: }
    @decay_rate = decay_rate
    @generation = 0
  end
  
  def record(pattern, score)
    key = pattern_hash(pattern)
    
    if @patterns[key]
      entry = @patterns[key]
      entry[:count] += 1
      entry[:success_rate] = entry[:success_rate] * 0.8 + score * 0.2
      entry[:last_seen] = @generation
    else
      @patterns[key] = { count: 1, success_rate: score, last_seen: @generation }
    end
  end
  
  def familiarity(pattern)
    key = pattern_hash(pattern)
    return 0.0 unless @patterns[key]
    
    entry = @patterns[key]
    age = @generation - entry[:last_seen]
    
    # Decay familiarity over time
    (entry[:count] / 10.0).clamp(0, 1) * (@decay_rate ** age)
  end
  
  def bias_for(pattern)
    key = pattern_hash(pattern)
    return 0.5 unless @patterns[key]
    @patterns[key][:success_rate]
  end
  
  def advance_generation
    @generation += 1
  end
end
```

## Self-Involution Engine

The core evolutionary loop:

```ruby
class SelfInvolution
  attr_reader :history, :intuition_bank
  
  def initialize(max_generations: 50, target_score: 0.85)
    @max_generations = max_generations
    @target_score = target_score
    @evaluator = Evaluator.new
    @intuition_bank = IntuitionBank.new
    @history = []
  end
  
  def evolve(initial_state)
    current = initial_state
    
    @max_generations.times do |gen|
      @intuition_bank.advance_generation
      
      # TRIFURCATE
      candidates = [
        { op: :expand, state: Trifurcate.expand(current) },
        { op: :mutate, state: Trifurcate.mutate(current) },
        { op: :transpose, state: Trifurcate.transpose(current) }
      ]
      
      # EVALUATE each
      evaluations = candidates.map do |c|
        eval_result = @evaluator.evaluate(c[:state])
        c.merge(evaluation: eval_result)
      end
      
      # ARGMAX select
      best = evaluations.max_by { |e| e[:evaluation][:total] }
      
      @history << {
        generation: gen,
        candidates: evaluations.map { |e| { op: e[:op], score: e[:evaluation][:total] } },
        selected: best[:op],
        score: best[:evaluation][:total]
      }
      
      current = best[:state]
      
      # FIXED POINT CHECK: ι∘ι = id?
      if best[:evaluation][:total] >= @target_score
        puts "  ✓ Fixed point reached at generation #{gen}"
        puts "    Score: #{best[:evaluation][:total].round(3)}"
        break
      end
      
      # Progress indicator
      if gen % 10 == 0
        puts "  Gen #{gen}: score=#{best[:evaluation][:total].round(3)} op=#{best[:op]}"
      end
    end
    
    current
  end
end
```

## Usage

### Command Line

```bash
# Full jungle showcase (3 phases)
just jungle

# Quick single evolution
just jungle-quick

# Tempo variations
just jungle-slow   # 140 BPM
just jungle-fast   # 185 BPM
```

### Ruby API

```ruby
require_relative 'lib/jungle_involution'

# Build evolved pattern
pattern = JungleInvolution::JunglePatternBuilder.build(
  duration: 16.0,
  generations: 30
)

# Access evolution history
involution = JungleInvolution::SelfInvolution.new(max_generations: 50)
initial = JungleInvolution::UIState.new(break_pattern: [...], bass_pattern: [...])
evolved = involution.evolve(initial)

# See what happened
involution.history.each do |gen|
  puts "Gen #{gen[:generation]}: #{gen[:selected]} → #{gen[:score].round(3)}"
end
```

## Convergence

The system converges when:
1. Score exceeds target threshold (default: 0.85)
2. Maximum generations reached
3. Score stops improving (delta < ε)

Typical convergence: 15-30 generations for score > 0.8

## Musical Characteristics

The evolved patterns tend to have:
- **Syncopated rhythms**: Off-grid hits from the chaos sources
- **Dynamic density**: Builds and releases from expansion/thinning
- **Bass weight**: Strong sub frequencies in half-time
- **Organic feel**: Never perfectly quantized
- **Structural variety**: Different from bar to bar

## References

- **Goldie, Metalheadz**: Early jungle production techniques
- **Reinforced Records**: Amen break manipulation
- **Hofstadter, D.**: Strange loops and self-reference
- **Kauffman, S.**: Self-organization in complex systems
