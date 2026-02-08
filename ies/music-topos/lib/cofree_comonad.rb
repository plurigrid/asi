# lib/cofree_comonad.rb
# Cofree Comonad (Matter) - Behavior trees / environments
#
# Based on Libkind & Spivak's "Pattern Runs on Matter" (ACT 2024):
# - Cofree comonad 𝔠q represents q-behavior trees (non-terminating)
# - Matter responds with decisions at each juncture
# - Memoizes all possible futures

module CofreeComonad
  # Cofree f a = a :< f (Cofree f a)
  #
  # - head: the current observable value
  # - tail: a functorful of possible futures
  class Cofree
    attr_reader :head, :tail
    
    def initialize(head, tail)
      @head = head
      @tail = tail
    end
    
    # Extract: get the current observation
    # This is the counit: Cofree f a -> a
    def extract
      @head
    end
    
    # Extend: apply a function at every position
    # (Cofree f a -> b) -> Cofree f a -> Cofree f b
    def extend(&f)
      Cofree.new(f.call(self), @tail&.fmap { |cf| cf.extend(&f) })
    end
    
    # Duplicate: replace each head with its subtree
    # Cofree f a -> Cofree f (Cofree f a)
    def duplicate
      extend { |cf| cf }
    end
    
    # Get the path through the structure using a selector
    def telescope(&selector)
      Enumerator.new do |yielder|
        current = self
        loop do
          yielder << current.extract
          break unless current.tail
          current = selector.call(current.tail)
          break unless current
        end
      end
    end
  end
  
  # ============================================================================
  # COITERATION - Building Cofree from a seed
  # ============================================================================
  
  # Build an infinite Cofree from a seed
  # (a -> f a) -> a -> Cofree f a
  def self.coiter(seed, &psi)
    tail = psi.call(seed)
    tail_cofree = tail&.fmap { |next_seed| coiter(next_seed, &psi) }
    Cofree.new(seed, tail_cofree)
  end
  
  # ============================================================================
  # MUSICAL MATTER TYPES
  # ============================================================================
  
  # Wrapper for functor values in Matter
  class MatterResponse
    attr_reader :value, :continue
    
    def initialize(value, continue = nil)
      @value = value
      @continue = continue
    end
    
    def fmap(&f)
      MatterResponse.new(@value, @continue ? f.call(@continue) : nil)
    end
  end
  
  # Complete musical environment state
  class MusicalMatter
    attr_accessor :tempo, :timbre, :volume, :beat, :time_ns, :play_fn,
                  :harmonic_key, :harmonic_function, :transforms, :conditions
    
    def initialize(tempo: 90, timbre: :sine, volume: 0.5, beat: 0,
                   harmonic_key: :C_major, harmonic_function: :tonic,
                   play_fn: nil, transforms: {}, conditions: {})
      @tempo = tempo
      @timbre = timbre
      @volume = volume
      @beat = beat
      @time_ns = Process.clock_gettime(Process::CLOCK_MONOTONIC, :nanosecond)
      @play_fn = play_fn || method(:default_play)
      @harmonic_key = harmonic_key
      @harmonic_function = harmonic_function
      @transforms = default_transforms.merge(transforms)
      @conditions = default_conditions.merge(conditions)
    end
    
    def default_play(pitches, duration, amplitude)
      pitches = [pitches] unless pitches.is_a?(Array)
      puts "♪ Playing #{pitches.map { |p| midi_to_note(p) }.join(',')} " \
           "for #{duration} beats at amp #{amplitude}"
    end
    
    def midi_to_note(midi)
      notes = %w[C C# D D# E F F# G G# A A# B]
      octave = (midi / 12) - 1
      note = notes[midi % 12]
      "#{note}#{octave}"
    end
    
    def default_transforms
      {
        transpose: ->(target, semitones) { target.map { |p| p + semitones } },
        invert: ->(target, axis) { target.map { |p| 2 * axis - p } },
        retrograde: ->(target) { target.reverse }
      }
    end
    
    def default_conditions
      {
        in_tonic?: ->(matter) { matter.harmonic_function == :tonic },
        cadence_ready?: ->(matter) { matter.harmonic_function == :dominant }
      }
    end
    
    def dup
      MusicalMatter.new(
        tempo: @tempo,
        timbre: @timbre,
        volume: @volume,
        beat: @beat,
        harmonic_key: @harmonic_key,
        harmonic_function: @harmonic_function,
        play_fn: @play_fn,
        transforms: @transforms.dup,
        conditions: @conditions.dup
      )
    end
    
    def advance(duration)
      new_matter = dup
      new_matter.beat += duration
      new_matter.time_ns += (duration * 60.0 / @tempo * 1e9).to_i
      new_matter
    end
  end
  
  # ============================================================================
  # STREAMING MATTER
  # ============================================================================
  
  # Create an infinite stream of matter states
  def self.matter_stream(initial_state)
    Enumerator.new do |yielder|
      state = initial_state
      loop do
        yielder << state
        state = yield_next_state(state)
      end
    end
  end
  
  def self.yield_next_state(state)
    state.advance(1)  # Advance by 1 beat
  end
  
  # Create a performance matter stream
  def self.performance_matter(tempo: 90, timbre: :sine, volume: 0.5, &play_fn)
    initial = MusicalMatter.new(
      tempo: tempo,
      timbre: timbre,
      volume: volume,
      play_fn: play_fn
    )
    matter_stream(initial)
  end
end
