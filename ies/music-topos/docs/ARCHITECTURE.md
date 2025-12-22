# Architecture: Pattern Runs on Matter

**Categorical Foundations for Generative Music**

This document describes the core architecture of Music Topos, based on [Libkind & Spivak's "Pattern Runs on Matter" (ACT 2024)](https://arxiv.org/abs/2401.13203).

## Overview

Music Topos models composition as:

```
Pattern ⊗ Matter → ScoreEvents
```

Where:
- **Pattern** (Free Monad) = terminating decision tree of musical actions
- **Matter** (Cofree Comonad) = non-terminating environment/context
- **⊗** (Module Action) = how patterns consume from matter

This separation provides clean compositional semantics: patterns describe *what* to play, matter provides *how* to play it.

## Free Monad (Pattern)

### Mathematical Definition

Given a functor `F`, the Free Monad `Free F A` is:

```
Free F A = Pure A | Suspend (F (Free F A))
```

In Music Topos, `F` is the musical instruction functor.

### Implementation

```ruby
# lib/free_monad.rb

module FreeMonad
  # Base class for Free monad values
  class Free
    def pure?
      is_a?(Pure)
    end
    
    def bind(&f)
      raise NotImplementedError
    end
  end
  
  # Pure value - computation complete
  class Pure < Free
    attr_reader :value
    
    def initialize(value)
      @value = value
    end
    
    def bind(&f)
      f.call(@value)
    end
  end
  
  # Suspended computation - more work to do
  class Suspend < Free
    attr_reader :instruction
    
    def initialize(instruction)
      @instruction = instruction
    end
    
    def bind(&f)
      Suspend.new(@instruction.fmap { |free| free.bind(&f) })
    end
  end
end
```

### Musical Instruction Functor

The functor `F` provides these instructions:

| Instruction | Parameters | Purpose |
|-------------|------------|---------|
| `PlayNote` | pitch, duration, amplitude | Single note |
| `PlayChord` | pitches, duration, amplitude | Multiple simultaneous notes |
| `Rest` | duration | Silence |
| `Sequence` | [actions] | Sequential composition |
| `Parallel` | [voices] | Polyphonic composition |
| `Branch` | condition, then, else | Conditional logic |
| `Transform` | transformation, target | Apply musical transformation |

### DSL

The DSL provides convenient constructors:

```ruby
extend FreeMonad::DSL

# Build a pattern
pattern = sequence!(
  play_note!(60, 1.0, 0.4),      # C4, 1 beat, 40% volume
  rest!(0.5),
  play_chord!([60, 64, 67], 2.0, 0.3),  # C major triad
  parallel!(
    play_note!(48, 4.0, 0.2),    # Bass drone
    sequence!(
      play_note!(60, 2.0, 0.3),
      play_note!(64, 2.0, 0.3)
    )
  )
)
```

### Monad Laws

The Free Monad satisfies the monad laws:

1. **Left Identity**: `pure(a).bind(f) == f(a)`
2. **Right Identity**: `m.bind(pure) == m`
3. **Associativity**: `m.bind(f).bind(g) == m.bind(x -> f(x).bind(g))`

These ensure pattern composition is well-behaved.

## Cofree Comonad (Matter)

### Mathematical Definition

Given a functor `G`, the Cofree Comonad `Cofree G A` is:

```
Cofree G A = (A, G (Cofree G A))
```

A pair of:
- Current value (head)
- Potential future values (tail)

### Implementation

```ruby
# lib/cofree_comonad.rb

module CofreeComonad
  class Cofree
    attr_reader :head, :tail
    
    def initialize(head, tail)
      @head = head
      @tail = tail  # Lazy: -> { next Cofree }
    end
    
    def extract
      @head
    end
    
    def extend(&f)
      Cofree.new(f.call(self), -> { @tail.call.extend(&f) })
    end
  end
end
```

### Musical Matter

Matter provides the execution environment:

```ruby
class MusicalMatter < Cofree
  def initialize(tempo:, timbre:, volume:, play_fn: nil, capabilities: [])
    state = {
      tempo: tempo,           # BPM
      timbre: timbre,         # Synth type (:sine, :saw, :square)
      volume: volume,         # Master volume (0.0 - 1.0)
      beat: 0,                # Current beat position
      capabilities: capabilities  # [:osc, :wav, :midi]
    }
    
    super(state, -> { advance_beat(state) })
  end
  
  def advance_beat(state)
    MusicalMatter.new(
      tempo: state[:tempo],
      timbre: state[:timbre],
      volume: state[:volume],
      beat: state[:beat] + 1
    )
  end
end
```

### Comonad Laws

The Cofree Comonad satisfies:

1. **Left Identity**: `w.extend(extract) == w`
2. **Right Identity**: `w.extend(f).extract == f(w)`
3. **Associativity**: `w.extend(f).extend(g) == w.extend(x -> g(x.extend(f)))`

## Module Action (⊗)

### Definition

A **module action** of a monad `M` on a comonad `W` is a natural transformation:

```
⊗ : M × W → W
```

Satisfying coherence conditions that ensure the monad and comonad interact correctly.

### Implementation

```ruby
# lib/runs_on.rb

module RunsOn
  def self.to_score_events(pattern, matter, beat: 0)
    events = []
    interpret(pattern, matter, beat, events)
    events.sort_by { |e| e[:at] }
  end
  
  private
  
  def self.interpret(pattern, matter, beat, events)
    return if pattern.pure?
    
    instruction = pattern.instruction
    
    case instruction
    when FreeMonad::PlayNote
      events << emit_note(instruction, matter, beat)
      interpret(instruction.next_fn.call, matter, beat + instruction.duration, events)
      
    when FreeMonad::PlayChord
      events << emit_chord(instruction, matter, beat)
      interpret(instruction.next_fn.call, matter, beat + instruction.duration, events)
      
    when FreeMonad::Rest
      interpret(instruction.next_fn.call, matter, beat + instruction.duration, events)
      
    when FreeMonad::Sequence
      current_beat = beat
      instruction.actions.each do |action|
        sub_events = to_score_events(action, matter, beat: current_beat)
        events.concat(sub_events)
        current_beat += duration_of(sub_events)
      end
      
    when FreeMonad::Parallel
      instruction.voices.each do |voice|
        events.concat(to_score_events(voice, matter, beat: beat))
      end
    end
  end
  
  def self.emit_note(instruction, matter, beat)
    freq = midi_to_hz(instruction.pitch)
    amp = instruction.amplitude * matter.extract[:volume]
    
    {
      id: "note-#{beat}",
      at: beat,
      dur: instruction.duration,
      world_object: { world: :pitch_space, type: :note, value: instruction.pitch },
      audio: {
        frequencies: [freq],
        amplitude: amp,
        synth: matter.extract[:timbre].to_s
      }
    }
  end
end
```

### Event Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                         INTERPRETATION                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Pattern                Matter                 Events           │
│  ┌─────┐               ┌─────┐                ┌─────┐          │
│  │Seq  │               │tempo│                │     │          │
│  │├─Note├─────⊗────────│beat │───────────────►│Event│          │
│  │├─Chord              │vol  │                │Event│          │
│  │├─Rest               │     │                │Event│          │
│  │└─Para               └─────┘                │...  │          │
│  └─────┘                                      └─────┘          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## ScoreEvent

The output of interpretation is a stream of `ScoreEvent` records:

```ruby
# lib/score_event.rb

class ScoreEvent
  attr_reader :id, :at, :dur, :world_object, :audio
  
  def initialize(id:, at:, dur:, world_object:, audio:)
    @id = id              # Unique identifier
    @at = at              # Beat position (Float)
    @dur = dur            # Duration in beats (Float)
    @world_object = world_object  # Semantic content
    @audio = audio        # Audio parameters
  end
end
```

### World Object

The `world_object` field provides categorical semantics:

```ruby
{
  world: :pitch_space,      # Which topos
  type: :note,              # Object type
  value: 60,                # MIDI pitch or array of pitches
  morphisms: [:transpose, :invert]  # Available transformations
}
```

### Audio Parameters

The `audio` field provides synthesis parameters:

```ruby
{
  frequencies: [261.63],    # Hz (can be multiple for chords)
  amplitude: 0.4,           # 0.0 - 1.0
  synth: 'sine',            # Synth name
  envelope: { attack: 0.01, decay: 0.1, sustain: 0.5, release: 0.2 }
}
```

## Rendering

Events can be rendered in two modes:

### Realtime (OSC)

```ruby
RunsOn.run_realtime(pattern, matter) do |event|
  osc_sender.play_event(event)
end
```

### Batch (WAV)

```ruby
events = RunsOn.to_score_events(pattern, matter)
synth = AudioSynthesis.new(output_file: '/tmp/output.wav')
synth.render_score(events, tempo: 120)
```

## Compositionality

The key benefit of this architecture is **compositionality**:

### Pattern Composition

```ruby
# Patterns compose via sequence and parallel
intro = sequence!(play_note!(60, 1, 0.3), play_note!(64, 1, 0.3))
verse = sequence!(play_chord!([48, 52, 55], 4, 0.4))
full_song = sequence!(intro, verse, intro)

# Patterns compose via bind
pattern.bind { |result| next_pattern_based_on(result) }
```

### Matter Composition

```ruby
# Matter evolves through the comonad structure
matter.extend { |w| transform_environment(w) }
```

### Interpretation is a Functor

```
interpret : Pattern × Matter → [Event]
```

This functor preserves composition:

```
interpret(seq(p1, p2), m) = interpret(p1, m) ++ interpret(p2, m')
```

Where `m'` is the evolved matter after `p1`.

## Clojure Implementation

The same architecture is implemented in Clojure:

```clojure
;; src/music_topos/free_monad.clj

(defprotocol IFree
  (pure? [this])
  (fmap [this f])
  (bind [this f]))

(defrecord Pure [value]
  IFree
  (pure? [_] true)
  (bind [_ f] (f value)))

(defrecord Suspend [instruction]
  IFree
  (pure? [_] false)
  (bind [_ f]
    (Suspend. (fmap instruction #(bind % f)))))
```

## Further Reading

- [Libkind & Spivak, "Pattern Runs on Matter"](https://arxiv.org/abs/2401.13203)
- [Free Monads and Free Applicatives (Haskell Wiki)](https://wiki.haskell.org/Free_monad)
- [Cofree Comonads (School of Haskell)](https://www.schoolofhaskell.com/user/edwardk/heap/cofree-comonad)
- [Category Theory for Programmers (Milewski)](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
