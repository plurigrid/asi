# OPN Transcendental Synthesis

**17 Parallel Components for Hyperreal Electronic Music**

This document describes the Oneohtrix Point Never-inspired synthesis system, which layers 17 specialized components to create complex, evolving electronic music.

## Philosophy

OPN's music combines:
- **Hyperreal MIDI orchestration** — uncanny valley instruments
- **Granular microsound** — thousands of tiny particles
- **Collage structure** — abrupt section changes
- **Emotional repetition** — obsessive loops with subtle variation
- **Spectral processing** — timbral transformation

The system models these as **parallel categorical functors** that can be composed.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        TRANSCENDENTAL ORCHESTRATOR                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐               │
│  │Granular │ │ Eccojam │ │  MIDI   │ │ Vocoder │ │Arpeggios│               │
│  │         │ │         │ │Orchestra│ │         │ │         │               │
│  └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘               │
│       │          │          │          │          │                        │
│  ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐               │
│  │  Drone  │ │  Glitch │ │Dynamics │ │Polyrhythm│ │  Synth  │               │
│  │         │ │         │ │         │ │         │ │ Textures│               │
│  └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘               │
│       │          │          │          │          │                        │
│  ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐ ┌────┴────┐               │
│  │ Samples │ │Repetition│ │ Harmony │ │Structure│ │Spectral │               │
│  │         │ │         │ │         │ │         │ │         │               │
│  └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘               │
│       │          │          │          │          │                        │
│       └──────────┴──────────┴──────┬───┴──────────┴──────────┘              │
│                                    │                                        │
│                             ┌──────┴──────┐                                 │
│                             │   Spatial   │                                 │
│                             │             │                                 │
│                             └──────┬──────┘                                 │
│                                    │                                        │
│                                    ▼                                        │
│                           [ Score Events ]                                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## The 17 Components

### 1. Granular Microsound

Thousands of tiny sound particles:

```ruby
# lib/opn/granular.rb

class GrainCloud
  def initialize(center_pitch: 60, density: 100, scatter: 12, duration: 8.0)
    @center = center_pitch
    @density = density      # grains per second
    @scatter = scatter      # semitones
    @duration = duration
  end
  
  def generate
    events = []
    time = 0
    grain_interval = 1.0 / @density
    
    while time < @duration
      # Gaussian scatter around center
      pitch = @center + (rand_gaussian * @scatter / 3).round
      dur = 0.001 + rand * 0.049  # 1-50ms
      amp = 0.05 + rand * 0.15
      
      events << { at: time, pitch: pitch, dur: dur, amp: amp }
      time += grain_interval * (0.5 + rand)
    end
    
    events
  end
end

# Spectral smear across harmonic series
def self.spectral_smear(fundamental: 36, partials: 8, duration: 6.0)
  events = []
  partials.times do |n|
    freq_ratio = n + 1
    pitch = fundamental + (12 * Math.log2(freq_ratio)).round
    cloud = GrainCloud.new(center_pitch: pitch, density: 30 / (n + 1))
    events += cloud.generate
  end
  events
end
```

### 2. Eccojam / Plunderphonics

Chopped and looped fragments:

```ruby
# lib/opn/eccojam.rb

class ChopLoop
  def initialize(pitches, durations, loop_count: 4, decay: 0.95)
    @pitches = pitches
    @durations = durations
    @loop_count = loop_count
    @decay = decay
  end
  
  def generate
    events = []
    time = 0
    amp = 0.6
    
    @loop_count.times do |loop_idx|
      @pitches.zip(@durations).each do |pitch, dur|
        # Pitch drift down (tape degradation)
        drifted_pitch = pitch - (loop_idx * 0.1).round
        stretched_dur = dur * (1 + loop_idx * 0.05)
        
        events << { at: time, pitch: drifted_pitch, dur: stretched_dur, amp: amp }
        time += stretched_dur
      end
      amp *= @decay
    end
    
    events
  end
end

# Slowed sample (vaporwave style)
def self.slowed_sample(pitches, slowdown: 0.5)
  events = []
  pitches.each_with_index do |pitch, i|
    # Transpose down with speed
    transposed = pitch - (12 * Math.log2(1.0 / slowdown)).round
    events << { at: i * 0.5 / slowdown, pitch: transposed, dur: 1.0, amp: 0.4 }
  end
  events
end
```

### 3. Hyperreal MIDI Orchestra

Uncanny valley instruments:

```ruby
# lib/opn/midi_orchestra.rb

class HyperrealEnsemble
  RANGES = {
    violin: [55, 96], viola: [48, 84], cello: [36, 72], bass: [28, 55],
    flute: [60, 96], oboe: [58, 91], clarinet: [50, 89], bassoon: [34, 72],
    horn: [41, 77], trumpet: [55, 82], trombone: [40, 72], tuba: [29, 55]
  }
  
  def initialize(voices: [:violin, :cello, :horn])
    @voices = voices
  end
  
  def chord(root, quality: :major, duration: 2.0)
    intervals = case quality
      when :major then [0, 4, 7]
      when :minor then [0, 3, 7]
      when :maj7 then [0, 4, 7, 11]
      when :min7 then [0, 3, 7, 10]
    end
    
    events = []
    @voices.each_with_index do |voice, i|
      pitch = root + intervals[i % intervals.length]
      
      # Slight timing humanization
      events << {
        at: [rand * 0.02, 0].max,
        pitch: pitch,
        dur: duration * (0.9 + rand * 0.2),
        amp: 0.4 * (0.8 + rand * 0.4),
        voice: voice
      }
    end
    events
  end
end

# Uncanny strings with clusters
def self.uncanny_strings(root: 48, duration: 8.0)
  cluster = [root, root + 1, root + 4, root + 5, root + 7]
  cluster.each_with_index.map do |pitch, i|
    { at: i * 0.3, pitch: pitch, dur: duration - i * 0.3, amp: 0.25 - i * 0.03 }
  end
end
```

### 4. Vocoder / Voice Synthesis

Formant-based vocal simulation:

```ruby
# lib/opn/vocoder.rb

class VocoderVoice
  FORMANTS = {
    a: [730, 1090, 2440],
    e: [530, 1840, 2480],
    i: [270, 2290, 3010],
    o: [570, 840, 2410],
    u: [440, 1020, 2240]
  }
  
  def initialize(carrier_pitch: 48)
    @carrier = carrier_pitch
  end
  
  def vowel(v, duration: 1.0)
    formants = FORMANTS[v] || FORMANTS[:a]
    
    formants.each_with_index.map do |freq, i|
      pitch = @carrier + (12 * Math.log2(freq / 261.63)).round
      { at: 0, pitch: pitch.clamp(24, 96), dur: duration, amp: 0.3 / (i + 1) }
    end
  end
  
  def speak(vowels, duration_each: 0.5)
    events = []
    vowels.each_with_index do |v, i|
      vowel(v).each { |e| events << e.merge(at: i * duration_each) }
    end
    events
  end
end
```

### 5. Retro-Futurist Arpeggios

Classic synth patterns with filter sweeps:

```ruby
# lib/opn/arpeggios.rb

PATTERNS = {
  up: ->(notes) { notes },
  down: ->(notes) { notes.reverse },
  updown: ->(notes) { notes + notes[1..-2].reverse },
  random: ->(notes) { notes.shuffle },
  converge: ->(notes) {
    result = []
    (notes.length / 2.0).ceil.times do |i|
      result << notes[i]
      result << notes[-(i+1)] if i != notes.length - i - 1
    end
    result
  }
}

def self.filter_sweep_arp(chord, duration: 8.0)
  arp = Arpeggiator.new(chord, pattern: :updown, octaves: 3, rate: 0.0625)
  events = arp.generate(bars: (duration / 4).ceil)
  
  # Simulate filter sweep with amplitude
  events.each_with_index do |e, i|
    progress = e[:at] / duration
    filter_sim = Math.sin(progress * Math::PI)
    e[:amp] *= 0.5 + filter_sim * 0.5
  end
  
  events
end
```

### 6. Drone / Cathedral Space

Infinite sustained tones with harmonics:

```ruby
# lib/opn/drone.rb

class InfiniteDrone
  def initialize(root: 36, harmonics: 8)
    @root = root
    @harmonics = harmonics
  end
  
  def generate(duration: 32.0)
    events = [{ at: 0, pitch: @root, dur: duration, amp: 0.4 }]
    
    @harmonics.times do |n|
      ratio = n + 2
      pitch = @root + (12 * Math.log2(ratio)).round
      detune = (rand - 0.5) * 0.2  # Beating
      
      events << {
        at: rand * 0.5,
        pitch: pitch + detune,
        dur: duration - rand,
        amp: 0.3 / ratio
      }
    end
    
    events
  end
end
```

### 7. Glitch Interruptions

Buffer stutters and data corruption:

```ruby
# lib/opn/glitch.rb

def self.buffer_stutter(pitch, buffer_size: 0.05, repeats: 16)
  repeats.times.map do |i|
    {
      at: i * buffer_size,
      pitch: pitch + (rand > 0.8 ? rand(-12..12) : 0),
      dur: buffer_size * 0.9,
      amp: 0.4 * (1 - i * 0.03)
    }
  end
end

def self.bitcrush(events, bits: 4)
  step = 12.0 / (2 ** bits)
  events.map { |e| e.merge(pitch: (e[:pitch] / step).round * step) }
end

def self.corrupt(events, corruption: 0.3)
  events.map do |e|
    if rand < corruption
      e.merge(
        pitch: e[:pitch] + rand(-24..24),
        dur: e[:dur] * (0.1 + rand * 2),
        amp: rand * 0.5
      )
    else
      e
    end
  end
end
```

### 8. Extreme Dynamic Range

Sudden silences and loud impacts:

```ruby
# lib/opn/dynamics.rb

def self.hard_cut(events, at_time:)
  events.select { |e| e[:at] < at_time }
end

def self.emergence(events, duration:)
  events.map do |e|
    progress = [e[:at] / duration, 1.0].min
    e.merge(amp: e[:amp] * progress * progress)
  end
end

def self.breathing(events, cycle: 4.0)
  events.map do |e|
    phase = (e[:at] % cycle) / cycle
    breath = 0.3 + 0.7 * Math.sin(phase * Math::PI)
    e.merge(amp: e[:amp] * breath)
  end
end

def self.impact(pitch, duration: 0.5, amp: 0.9)
  [
    { at: 0, pitch: pitch, dur: duration, amp: amp },
    { at: 0, pitch: pitch - 12, dur: duration * 1.2, amp: amp * 0.8 },
    { at: 0, pitch: pitch + 12, dur: duration * 0.8, amp: amp * 0.6 }
  ]
end
```

### 9. Polyrhythmic Layers

Multiple time signatures simultaneously:

```ruby
# lib/opn/polyrhythm.rb

class PolyLayer
  def initialize(divisions)
    @divisions = divisions  # e.g., [3, 4, 5, 7]
  end
  
  def generate(duration: 16.0, pitches: nil)
    events = []
    
    @divisions.each_with_index do |div, layer|
      pitch = pitches ? pitches[layer % pitches.length] : 48 + layer * 7
      interval = duration / (div * 4)
      
      time = 0
      while time < duration
        events << { at: time, pitch: pitch, dur: interval * 0.5, amp: 0.25, layer: layer }
        time += interval
      end
    end
    
    events.sort_by { |e| e[:at] }
  end
end

# Phase shifting (Reich style)
def self.phase_shift(pattern, copies: 2, drift: 0.01)
  events = []
  copies.times do |c|
    offset = 0
    pattern.each do |e|
      events << e.merge(at: e[:at] + offset, amp: e[:amp] / copies)
      offset += drift
    end
  end
  events.sort_by { |e| e[:at] }
end
```

### 10. Synthesizer Textures

PWM pads, FM bells, supersaws:

```ruby
# lib/opn/synth_textures.rb

def self.pwm_pad(root: 48, duration: 8.0)
  events = []
  detunes = [-0.1, -0.05, 0, 0.05, 0.1]
  
  detunes.each do |d|
    events << { at: rand * 0.1, pitch: root + d, dur: duration, amp: 0.15 }
    events << { at: rand * 0.1, pitch: root + 7 + d, dur: duration, amp: 0.12 }
  end
  
  events
end

def self.fm_bell(pitch, duration: 2.0)
  events = [{ at: 0, pitch: pitch, dur: duration, amp: 0.4 }]
  
  # Inharmonic partials
  [1.4, 2.76, 5.4].each do |ratio|
    harm_pitch = pitch + (12 * Math.log2(ratio)).round
    events << { at: 0, pitch: harm_pitch.clamp(24, 96), dur: duration * 0.7, amp: 0.15 / ratio }
  end
  
  events
end

def self.supersaw(pitches, duration: 4.0)
  pitches.flat_map do |pitch|
    7.times.map do |i|
      { at: 0, pitch: pitch + (i - 3) * 0.08, dur: duration, amp: 0.08 }
    end
  end
end
```

### 11. Sample Manipulation

Time stretching and pitch shifting:

```ruby
# lib/opn/samples.rb

def self.reverse(events)
  return events if events.empty?
  max_time = events.map { |e| e[:at] + (e[:dur] || 0) }.max
  events.map { |e| e.merge(at: max_time - e[:at] - (e[:dur] || 0)) }.sort_by { |e| e[:at] }
end

def self.paulstretch(events, stretch: 8.0, density: 20)
  events.flat_map do |e|
    duration = (e[:dur] || 0.5) * stretch
    grains = (density * duration).to_i
    
    grains.times.map do
      {
        at: e[:at] * stretch + rand * duration,
        pitch: e[:pitch] + (rand - 0.5),
        dur: duration / density * 2,
        amp: e[:amp] * 0.3
      }
    end
  end.sort_by { |e| e[:at] }
end
```

### 12. Emotional Repetition

Obsessive loops with decay:

```ruby
# lib/opn/repetition.rb

def self.obsessive_loop(phrase, repetitions: 16, subtle_variation: true)
  events = []
  phrase_duration = phrase.map { |e| e[:at] + (e[:dur] || 0.5) }.max
  
  repetitions.times do |rep|
    phrase.each do |e|
      variation = subtle_variation ? {
        pitch: e[:pitch] + (rand > 0.9 ? [-1, 1].sample : 0),
        amp: e[:amp] * (0.95 + rand * 0.1)
      } : {}
      
      events << e.merge(variation).merge(at: e[:at] + rep * phrase_duration)
    end
  end
  
  events
end

def self.memory_fade(phrase, loops: 8)
  events = []
  phrase_duration = phrase.map { |e| e[:at] + (e[:dur] || 0.5) }.max
  
  loops.times do |l|
    decay = 1.0 - (l.to_f / loops) * 0.7
    phrase.each do |e|
      next if rand > decay + 0.3  # Notes disappear
      events << e.merge(
        at: e[:at] + l * phrase_duration,
        amp: e[:amp] * decay,
        pitch: e[:pitch] - (l * 0.1).round
      )
    end
  end
  
  events
end
```

### 13. Harmonic Language

Cluster chords and quartal voicing:

```ruby
# lib/opn/harmony.rb

CHORD_TYPES = {
  major: [0, 4, 7],
  minor: [0, 3, 7],
  maj9: [0, 4, 7, 11, 14],
  min11: [0, 3, 7, 10, 14, 17],
  cluster_tight: [0, 1, 2, 3],
  cluster_wide: [0, 2, 5, 7],
  quartal: [0, 5, 10, 15],
  split_5ths: [0, 7, 14, 21]
}

def self.chord(root, type: :major, duration: 2.0)
  intervals = CHORD_TYPES[type] || [0, 4, 7]
  intervals.map.with_index do |i, idx|
    {
      at: idx * 0.02,  # Slight strum
      pitch: (root + i).clamp(24, 96),
      dur: duration,
      amp: 0.4 / (idx * 0.1 + 1)
    }
  end
end
```

### 14. Structural Forms

Collage and arc forms:

```ruby
# lib/opn/structure.rb

class Collage
  def initialize
    @sections = []
  end
  
  def add_section(events, gap: 0.5)
    @sections << { events: events, gap: gap }
    self
  end
  
  def generate
    result = []
    time = 0
    
    @sections.each do |section|
      section[:events].each { |e| result << e.merge(at: e[:at] + time) }
      max_time = section[:events].map { |e| e[:at] + (e[:dur] || 0) }.max || 0
      time += max_time + section[:gap]
    end
    
    result
  end
end

def self.arc_form(a_events:, b_events:, climax_events:)
  # A - B - Climax - B' - A'
  result = []
  time = 0
  
  # A
  a_events.each { |e| result << e.merge(at: e[:at] + time) }
  time += duration_of(a_events) + 1
  
  # B
  b_events.each { |e| result << e.merge(at: e[:at] + time) }
  time += duration_of(b_events) + 1
  
  # Climax
  climax_events.each { |e| result << e.merge(at: e[:at] + time) }
  time += duration_of(climax_events) + 1
  
  # B' (transposed)
  b_events.each { |e| result << e.merge(at: e[:at] + time, pitch: e[:pitch] + 2) }
  time += duration_of(b_events) + 1
  
  # A' (quieter)
  a_events.each { |e| result << e.merge(at: e[:at] + time, amp: e[:amp] * 0.6) }
  
  result
end
```

### 15. Spectral Processing

Freeze and blur:

```ruby
# lib/opn/spectral.rb

def self.spectral_freeze(fundamental: 48, duration: 8.0, partials: 16)
  partials.times.map do |n|
    ratio = n + 1
    pitch = fundamental + (12 * Math.log2(ratio)).round
    amp = 0.3 / Math.sqrt(ratio) * (0.5 + rand * 0.5)
    
    { at: rand * 0.2, pitch: pitch.clamp(24, 96), dur: duration, amp: amp }
  end
end

def self.spectral_blur(events, blur_amount: 3)
  events.flat_map do |e|
    blur_amount.times.map do |b|
      offset = (b - blur_amount / 2) * 0.05
      {
        at: e[:at] + offset,
        pitch: e[:pitch] + (b - blur_amount / 2),
        dur: e[:dur] * 1.2,
        amp: e[:amp] / blur_amount
      }
    end
  end
end
```

### 16. Spatial Effects

Delay networks and reverb simulation:

```ruby
# lib/opn/spatial.rb

def self.delay_network(events, taps: 4, base_delay: 0.3, feedback: 0.6)
  result = events.dup
  
  taps.times do |tap|
    delay = base_delay * (tap + 1)
    amp_mult = feedback ** (tap + 1)
    
    events.each do |e|
      result << e.merge(at: e[:at] + delay, amp: e[:amp] * amp_mult)
    end
  end
  
  result.sort_by { |e| e[:at] }
end

def self.shimmer(events, density: 3, spread: 2.0)
  events.flat_map do |e|
    [e] + density.times.map do
      {
        at: e[:at] + rand * spread,
        pitch: e[:pitch] + 12 + rand(-2..2),
        dur: e[:dur] * 0.5,
        amp: e[:amp] * 0.2
      }
    end
  end
end
```

### 17. Transcendental Orchestrator

Combines all components:

```ruby
# lib/opn/transcendental.rb

class TranscendentalGenerator
  def initialize(seed: 42, duration: 120.0)
    @seed = seed
    @duration = duration
    srand(seed)
  end
  
  def generate
    events = []
    
    # Layer 1: Deep drone foundation
    events += Drone.evolving_drone(root: 36, duration: @duration)
    
    # Layer 2: Granular texture
    4.times do |i|
      start = i * @duration / 4
      cloud = Granular::GrainCloud.new(center_pitch: 60 + i * 7, density: 30)
      events += cloud.generate.map { |e| e.merge(at: e[:at] + start) }
    end
    
    # Layer 3: Harmonic progression
    progression = [[48, :maj9], [53, :min11], [41, :sus4], [48, :cluster_wide]]
    progression.each_with_index do |(root, type), i|
      Harmony.chord(root, type: type).each do |e|
        events << e.merge(at: e[:at] + i * @duration / 4)
      end
    end
    
    # Layer 4: Arpeggios
    arp_events = Arpeggios.filter_sweep_arp([48, 52, 55, 60], duration: @duration / 2)
    events += arp_events
    
    # Layer 5: Glitch interruptions
    5.times do
      glitch_time = rand * @duration
      events += Glitch.buffer_stutter(60 + rand(-12..12))
        .map { |e| e.merge(at: e[:at] + glitch_time) }
    end
    
    # Layer 6: Dynamics
    events = Dynamics.breathing(events, cycle: 16.0)
    
    # Layer 7: Spatial
    events = Spatial.shimmer(events, density: 5)
    
    events.sort_by { |e| e[:at] }
  end
end
```

## Album Presets

### Garden of Delete

Uncanny MIDI + vocoder + glitch:

```ruby
def self.garden_of_delete(duration: 90.0)
  events = MidiOrchestra.uncanny_strings(root: 48, duration: duration / 2)
  events += Vocoder.synth_choir(root: 60, duration: duration / 4)
    .map { |e| e.merge(at: e[:at] + duration / 2) }
  events = Glitch.corrupt(events, corruption: 0.1)
  Spectral.spectral_blur(events, blur_amount: 2)
end
```

### R Plus Seven

Granular + orchestral collage:

```ruby
def self.r_plus_seven(duration: 120.0)
  events = Granular.spectral_smear(fundamental: 36, partials: 12)
  
  ensemble = MidiOrchestra::HyperrealEnsemble.new(voices: [:violin, :viola, :cello])
  events += ensemble.progression([48, 53, 45, 50], [:maj9, :min11, :sus4, :quartal])
  
  Samples.paulstretch(events, stretch: 1.5, density: 15)
end
```

### Age Of

Vocal + polyrhythm + eccojam:

```ruby
def self.age_of(duration: 60.0)
  voice = Vocoder::VocoderVoice.new(carrier_pitch: 48)
  events = voice.speak([:a, :e, :i, :o, :u] * 4)
  
  poly = Polyrhythm::PolyLayer.new([3, 4, 5, 7])
  events += poly.generate(duration: duration, pitches: [48, 55, 60, 67])
  
  phrase = (0..7).map { |i| { at: i * 0.25, pitch: 60 + [0, 2, 4, 5, 7, 5, 4, 2][i] } }
  events += Eccojam::ChopLoop.new(phrase.map { |e| e[:pitch] }, [0.2] * 8).generate
    .map { |e| e.merge(at: e[:at] + duration / 2) }
  
  Dynamics.emergence(Spatial.room(events, size: :cathedral), duration: duration / 4)
end
```

## Usage

### Command Line

```bash
# Full transcendental piece
just opn-transcendental

# Album presets
just opn-garden     # Garden of Delete style
just opn-rplus7     # R Plus Seven style
just opn-ageof      # Age Of style

# List components
just opn-components
```

### Ruby API

```ruby
require_relative 'lib/opn/transcendental'

# Full piece
events = OPN::Transcendental.transcendental_piece(seed: 42, duration: 180.0)

# Album presets
garden = OPN::Transcendental.garden_of_delete(duration: 90.0)
rplus7 = OPN::Transcendental.r_plus_seven(duration: 120.0)
ageof = OPN::Transcendental.age_of(duration: 60.0)

# Individual components
cloud = OPN::Granular::GrainCloud.new(center_pitch: 60, density: 100)
drone = OPN::Drone::InfiniteDrone.new(root: 36)
```

## References

- **Oneohtrix Point Never**: _R Plus Seven_, _Garden of Delete_, _Age Of_
- **Curtis Roads**: _Microsound_ (granular synthesis theory)
- **Vaporwave**: Eccojam aesthetics
- **Paulstretch**: Extreme time stretching algorithm
