# lib/free_monad.rb
# Free Monad (Pattern) - Decision trees for musical actions
#
# Based on Libkind & Spivak's "Pattern Runs on Matter" (ACT 2024):
# - Free monad 𝔪p represents terminating decision trees
# - Pattern determines how a situation can unfold
# - Each position is a question, directions are possible answers

module FreeMonad
  # Base class for Free monad values
  class Free
    def pure?
      is_a?(Pure)
    end
    
    def bind(&f)
      raise NotImplementedError
    end
    
    def map(&f)
      bind { |a| Pure.new(f.call(a)) }
    end
    
    def flatten
      bind { |x| x }
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
    
    def to_s
      "Pure(#{@value})"
    end
  end
  
  # Suspended computation - more work to do
  class Suspend < Free
    attr_reader :instruction
    
    def initialize(instruction)
      @instruction = instruction
    end
    
    def bind(&f)
      # fmap the bind into the instruction's continuation
      Suspend.new(@instruction.fmap { |free| free.bind(&f) })
    end
    
    def to_s
      "Suspend(#{@instruction.class.name.split('::').last})"
    end
  end
  
  # ============================================================================
  # MUSICAL INSTRUCTION FUNCTOR
  # ============================================================================
  
  # Base class for instructions
  class Instruction
    def fmap(&f)
      raise NotImplementedError
    end
  end
  
  # Play a single note
  class PlayNote < Instruction
    attr_reader :pitch, :duration, :amplitude, :next_fn
    
    def initialize(pitch, duration, amplitude, &next_fn)
      @pitch = pitch
      @duration = duration
      @amplitude = amplitude
      @next_fn = next_fn || -> { Pure.new(nil) }
    end
    
    def fmap(&f)
      PlayNote.new(@pitch, @duration, @amplitude) { f.call(@next_fn.call) }
    end
  end
  
  # Play a chord (multiple notes simultaneously)
  class PlayChord < Instruction
    attr_reader :pitches, :duration, :amplitude, :next_fn
    
    def initialize(pitches, duration, amplitude, &next_fn)
      @pitches = pitches
      @duration = duration
      @amplitude = amplitude
      @next_fn = next_fn || -> { Pure.new(nil) }
    end
    
    def fmap(&f)
      PlayChord.new(@pitches, @duration, @amplitude) { f.call(@next_fn.call) }
    end
  end
  
  # Rest (silence)
  class Rest < Instruction
    attr_reader :duration, :next_fn
    
    def initialize(duration, &next_fn)
      @duration = duration
      @next_fn = next_fn || -> { Pure.new(nil) }
    end
    
    def fmap(&f)
      Rest.new(@duration) { f.call(@next_fn.call) }
    end
  end
  
  # Apply a musical transformation
  class Transform < Instruction
    attr_reader :transformation, :target, :next_fn
    
    def initialize(transformation, target, &next_fn)
      @transformation = transformation
      @target = target
      @next_fn = next_fn || ->(result) { Pure.new(result) }
    end
    
    def fmap(&f)
      Transform.new(@transformation, @target) { |result| f.call(@next_fn.call(result)) }
    end
  end
  
  # Conditional branch
  class Branch < Instruction
    attr_reader :condition, :then_branch, :else_branch
    
    def initialize(condition, then_branch, else_branch)
      @condition = condition
      @then_branch = then_branch
      @else_branch = else_branch
    end
    
    def fmap(&f)
      Branch.new(@condition, f.call(@then_branch), f.call(@else_branch))
    end
  end
  
  # Sequential composition
  class Sequence < Instruction
    attr_reader :actions
    
    def initialize(actions)
      @actions = actions
    end
    
    def fmap(&f)
      Sequence.new(@actions.map { |a| f.call(a) })
    end
  end
  
  # Parallel composition (polyphony)
  class Parallel < Instruction
    attr_reader :voices
    
    def initialize(voices)
      @voices = voices
    end
    
    def fmap(&f)
      Parallel.new(@voices.map { |v| f.call(v) })
    end
  end
  
  # ============================================================================
  # DSL CONSTRUCTORS
  # ============================================================================
  
  module DSL
    def pure(x)
      Pure.new(x)
    end
    
    def play_note!(pitch, duration, amplitude)
      Suspend.new(PlayNote.new(pitch, duration, amplitude))
    end
    
    def play_chord!(pitches, duration, amplitude)
      Suspend.new(PlayChord.new(pitches, duration, amplitude))
    end
    
    def rest!(duration)
      Suspend.new(Rest.new(duration))
    end
    
    def transform!(transformation, target)
      Suspend.new(Transform.new(transformation, target))
    end
    
    def branch!(condition, then_branch, else_branch)
      Suspend.new(Branch.new(condition, then_branch, else_branch))
    end
    
    def sequence!(*actions)
      Suspend.new(Sequence.new(actions))
    end
    
    def parallel!(*voices)
      Suspend.new(Parallel.new(voices))
    end
  end
  
  # ============================================================================
  # FOLD / INTERPRETER
  # ============================================================================
  
  def self.fold(pattern, &interpreter)
    if pattern.pure?
      pattern.value
    else
      interpreter.call(pattern.instruction.fmap { |p| fold(p, &interpreter) })
    end
  end
end

# ============================================================================
# EXAMPLE: INITIAL WORLD AS FREE MONAD PATTERN
# ============================================================================

class InitialWorldPattern
  extend FreeMonad::DSL
  
  def self.build
    sequence!(
      # 1. Initial pitch
      play_note!(60, 2.0, 0.3),
      
      # 2. Chromatic scale
      sequence!(
        *((60..71).map { |p| play_note!(p, 0.08, 0.2) })
      ),
      
      # 3. Harmonic functions T → S → D → T
      sequence!(
        play_chord!([60, 64, 67], 0.8, 0.2),  # Tonic
        play_chord!([65, 69, 72], 0.8, 0.2),  # Subdominant
        play_chord!([67, 71, 74], 0.8, 0.2),  # Dominant
        play_chord!([60, 64, 67], 0.8, 0.2)   # Tonic return
      ),
      
      # 4. Circle of fifths
      sequence!(
        play_note!(60, 0.5, 0.25),  # C
        play_note!(67, 0.5, 0.25),  # G
        play_note!(62, 0.5, 0.25),  # D
        play_note!(69, 0.5, 0.25)   # A
      )
    )
  end
end
