# lib/parametrised_optics.rb
#
# Parametrised Optics for Musical Cybernetics
#
# "Parametrised optics model cybernetic systems, namely dynamical systems
#  steered by one or more agents. Then ⊛ represents agency being exerted on systems"
#
# In music:
# - The SYSTEM is the evolving composition (state space of pitches, harmonies)
# - The AGENT is the composer/performer making choices
# - ⊛ (para) represents musical agency: how choices shape the composition
#
# Optic structure:
#   Optic(S, S', A, A') = ∃M. (S → M × A) × (M × A' → S')
#   - S = input state (current musical context)
#   - A = focus (what we're modifying: pitch, chord, rhythm)
#   - A' = updated focus (the modification)
#   - S' = output state (new musical context)
#   - M = residual (what's preserved: key, meter, texture)
#
# Para construction:
#   Para(C)(A, B) = C(P ⊗ A, B)  for parameter object P
#   ⊛ : Para(C)(A, B) × Para(C)(B, C) → Para(C)(A, C)

module ParametrisedOptics
  # Base Optic: bidirectional transformation
  # forward: S → (M, A)     -- extract focus and residual
  # backward: (M, A') → S'  -- recombine with modified focus
  class Optic
    attr_reader :forward, :backward, :name

    def initialize(name, forward:, backward:)
      @name = name
      @forward = forward
      @backward = backward
    end

    # Apply optic: extract focus from state
    def get(state)
      residual, focus = @forward.call(state)
      { residual: residual, focus: focus }
    end

    # Apply optic: update state with new focus
    def put(residual, new_focus)
      @backward.call(residual, new_focus)
    end

    # Compose optics: self then other
    def compose(other)
      Optic.new(
        "#{@name} ∘ #{other.name}",
        forward: ->(s) {
          r1, a = @forward.call(s)
          r2, b = other.forward.call(a)
          [[r1, r2], b]
        },
        backward: ->((r1, r2), b_prime) {
          a_prime = other.backward.call(r2, b_prime)
          @backward.call(r1, a_prime)
        }
      )
    end

    def to_s
      "Optic(#{@name})"
    end
  end

  # Lens: optic for product types (access a component)
  # Lens(S, A) when S ≅ A × R for some residual R
  class Lens < Optic
    def self.create(name, get:, set:)
      new(
        name,
        forward: ->(s) { [s, get.call(s)] },  # Residual is whole state
        backward: ->(s, a) { set.call(s, a) }
      )
    end
  end

  # Prism: optic for sum types (optional access)
  # Prism(S, A) when S ≅ A + R for some residual R
  class Prism < Optic
    def self.create(name, match:, build:)
      new(
        name,
        forward: ->(s) {
          result = match.call(s)
          result ? [:matched, result] : [:unmatched, s]
        },
        backward: ->(tag, a) {
          tag == :matched ? build.call(a) : a
        }
      )
    end
  end

  # Parametrised morphism: Para(C)(A, B) = C(P ⊗ A, B)
  # P is the parameter (agent's choice space)
  # The morphism takes (parameter, input) → output
  class Para
    attr_reader :name, :param_space, :morphism

    def initialize(name, param_space:, &morphism)
      @name = name
      @param_space = param_space
      @morphism = morphism
    end

    # Apply with specific parameter
    def apply(param, input)
      @morphism.call(param, input)
    end

    # ⊛ operator: sequential composition of parametrised morphisms
    # Para(A,B) ⊛ Para(B,C) → Para(A,C)
    # Agent exerts control at each stage
    def para_compose(other)
      Para.new(
        "#{@name} ⊛ #{other.name}",
        param_space: [@param_space, other.param_space]
      ) do |(p1, p2), input|
        intermediate = @morphism.call(p1, input)
        other.morphism.call(p2, intermediate)
      end
    end
    alias_method :⊛, :para_compose

    # Parallel composition: run two para morphisms on product
    def para_tensor(other)
      Para.new(
        "#{@name} ⊗ #{other.name}",
        param_space: [@param_space, other.param_space]
      ) do |(p1, p2), (a, b)|
        [@morphism.call(p1, a), other.morphism.call(p2, b)]
      end
    end

    def to_s
      "Para[#{@param_space}](#{@name})"
    end
  end

  # Cybernetic System: dynamical system with agent control
  # state' = dynamics(state, action)
  # action = policy(state, parameter)
  class CyberneticSystem
    attr_reader :state, :dynamics, :policy, :history

    def initialize(initial_state, dynamics:, policy:)
      @state = initial_state
      @dynamics = dynamics  # (state, action) → state'
      @policy = policy      # Para morphism: (param, state) → action
      @history = [initial_state]
    end

    # Step the system with agent parameter
    def step(parameter)
      action = @policy.apply(parameter, @state)
      @state = @dynamics.call(@state, action)
      @history << @state
      { state: @state, action: action }
    end

    # Run for n steps with parameter sequence
    def run(parameters)
      parameters.map { |p| step(p) }
    end

    # Feedback loop: agent observes state
    def feedback_loop(observer, controller, steps: 10)
      steps.times.map do
        observation = observer.call(@state)
        parameter = controller.call(observation)
        step(parameter)
      end
    end
  end

  # ==========================================================================
  # MUSICAL OPTICS
  # ==========================================================================

  module Musical
    # Pitch Lens: focus on pitch in a note
    PITCH_LENS = Lens.create(
      "pitch",
      get: ->(note) { note[:pitch] },
      set: ->(note, p) { note.merge(pitch: p) }
    )

    # Duration Lens
    DURATION_LENS = Lens.create(
      "duration",
      get: ->(note) { note[:duration] },
      set: ->(note, d) { note.merge(duration: d) }
    )

    # Velocity Lens
    VELOCITY_LENS = Lens.create(
      "velocity",
      get: ->(note) { note[:velocity] },
      set: ->(note, v) { note.merge(velocity: v) }
    )

    # Chord Root Lens
    CHORD_ROOT_LENS = Lens.create(
      "root",
      get: ->(chord) { chord[:pitches]&.first || 0 },
      set: ->(chord, r) {
        interval_structure = chord[:pitches][1..-1].map { |p| p - chord[:pitches].first }
        new_pitches = [r] + interval_structure.map { |i| r + i }
        chord.merge(pitches: new_pitches)
      }
    )

    # Modulation Prism: optional key change
    MODULATION_PRISM = Prism.create(
      "modulation",
      match: ->(state) {
        state[:modulating] ? state[:target_key] : nil
      },
      build: ->(new_key) {
        { key: new_key, modulating: false }
      }
    )

    # Voice Leading Prism: match if smooth motion possible
    VOICE_LEADING_PRISM = Prism.create(
      "voice_leading",
      match: ->(transition) {
        from, to = transition[:from], transition[:to]
        motion = (to - from).abs
        motion <= 2 ? { from: from, to: to, motion: motion } : nil
      },
      build: ->(vl) { vl[:to] }
    )

    # ==========================================================================
    # PARAMETRISED MUSICAL TRANSFORMATIONS (Agency)
    # ==========================================================================

    # Transposition: agent chooses interval
    TRANSPOSE = Para.new(
      "transpose",
      param_space: (-12..12).to_a  # Semitone choices
    ) { |interval, pitch| (pitch + interval) % 12 }

    # Harmonize: agent chooses chord type
    HARMONIZE = Para.new(
      "harmonize",
      param_space: [:major, :minor, :dim, :aug, :sus4]
    ) do |chord_type, root|
      intervals = case chord_type
                  when :major then [0, 4, 7]
                  when :minor then [0, 3, 7]
                  when :dim   then [0, 3, 6]
                  when :aug   then [0, 4, 8]
                  when :sus4  then [0, 5, 7]
                  end
      intervals.map { |i| (root + i) % 12 }
    end

    # Rhythmic Transformation: agent chooses subdivision
    RHYTHMIZE = Para.new(
      "rhythmize",
      param_space: [1, 2, 3, 4, 6, 8]  # Subdivision factors
    ) { |subdivision, duration| duration / subdivision.to_f }

    # Voice Leading: agent chooses direction
    VOICE_LEAD = Para.new(
      "voice_lead",
      param_space: [:up, :down, :nearest]
    ) do |direction, (from, to)|
      motion = case direction
               when :up then (to - from) % 12
               when :down then -((from - to) % 12)
               when :nearest then 
                 up = (to - from) % 12
                 down = (from - to) % 12
                 up <= down ? up : -down
               end
      from + motion
    end

    # Intensity: agent chooses dynamic level
    INTENSIFY = Para.new(
      "intensify",
      param_space: [:ppp, :pp, :p, :mp, :mf, :f, :ff, :fff]
    ) do |dynamic, velocity|
      base = { ppp: 16, pp: 32, p: 48, mp: 64, 
               mf: 80, f: 96, ff: 112, fff: 127 }[dynamic]
      (velocity * 0.3 + base * 0.7).round
    end

    # ==========================================================================
    # COMPOSITE AGENCY: ⊛ compositions
    # ==========================================================================

    # Full melodic transformation: transpose then harmonize
    def self.melodic_agency
      TRANSPOSE.para_compose(HARMONIZE)
    end

    # Expressive agency: rhythmize then intensify
    def self.expressive_agency
      RHYTHMIZE.para_compose(INTENSIFY)
    end

    # ==========================================================================
    # CYBERNETIC COMPOSITION SYSTEM
    # ==========================================================================

    # Musical state: current compositional context
    def self.create_compositional_system(initial_state)
      dynamics = ->(state, action) {
        case action[:type]
        when :add_note
          notes = state[:notes] + [action[:note]]
          state.merge(notes: notes, time: state[:time] + action[:note][:duration])
        when :modulate
          state.merge(key: action[:target], modulating: true)
        when :cadence
          state.merge(cadenced: true, function: :tonic)
        else
          state
        end
      }

      policy = Para.new(
        "composition_policy",
        param_space: [:develop, :contrast, :return, :cadence]
      ) do |intention, state|
        case intention
        when :develop
          # Continue in current direction
          last_pitch = state[:notes].last&.dig(:pitch) || 60
          { type: :add_note, note: { pitch: last_pitch + rand(-3..3), duration: 0.5 } }
        when :contrast
          # Jump to distant pitch
          last_pitch = state[:notes].last&.dig(:pitch) || 60
          { type: :add_note, note: { pitch: last_pitch + rand(5..8) * [1, -1].sample, duration: 0.5 } }
        when :return
          # Move toward tonic
          tonic = state[:key] || 0
          { type: :add_note, note: { pitch: tonic + 60, duration: 0.5 } }
        when :cadence
          { type: :cadence }
        end
      end

      CyberneticSystem.new(initial_state, dynamics: dynamics, policy: policy)
    end
  end

  # ==========================================================================
  # OPTIC ↔ GIRARD CONNECTION
  # ==========================================================================

  module GirardOptics
    # Linear logic connectives as optic operations
    # ⊗ (tensor) → parallel composition of optics
    # ⅋ (par) → choice between optics
    # ! (bang) → replicate optic
    # ? (quest) → optional application

    def self.tensor(optic1, optic2)
      Optic.new(
        "#{optic1.name} ⊗ #{optic2.name}",
        forward: ->((s1, s2)) {
          r1, a1 = optic1.forward.call(s1)
          r2, a2 = optic2.forward.call(s2)
          [[r1, r2], [a1, a2]]
        },
        backward: ->((r1, r2), (a1, a2)) {
          [optic1.backward.call(r1, a1), optic2.backward.call(r2, a2)]
        }
      )
    end

    def self.par(optic1, optic2, choice_fn)
      Optic.new(
        "#{optic1.name} ⅋ #{optic2.name}",
        forward: ->(s) {
          if choice_fn.call(s) == :left
            [:left, optic1.forward.call(s)]
          else
            [:right, optic2.forward.call(s)]
          end
        },
        backward: ->(tag_and_residual, a) {
          tag, residual = tag_and_residual
          if tag == :left
            optic1.backward.call(residual, a)
          else
            optic2.backward.call(residual, a)
          end
        }
      )
    end

    def self.bang(optic, n)
      # Replicate optic n times
      Optic.new(
        "!#{optic.name}",
        forward: ->(states) {
          states.map { |s| optic.forward.call(s) }.transpose
        },
        backward: ->(residuals, focuses) {
          residuals.zip(focuses).map { |r, a| optic.backward.call(r, a) }
        }
      )
    end

    def self.quest(optic)
      # Optional: apply if Some, pass through if None
      Optic.new(
        "?#{optic.name}",
        forward: ->(maybe_s) {
          maybe_s ? [:some, optic.forward.call(maybe_s)] : [:none, nil]
        },
        backward: ->(tag_and_residual, a) {
          tag, residual = tag_and_residual
          tag == :some ? optic.backward.call(residual, a) : nil
        }
      )
    end

    # Polarity-aware para composition
    # Positive → forward direction
    # Negative → backward direction
    def self.polarised_para(para, polarity)
      if polarity == :positive
        para
      else
        # Flip the morphism direction
        Para.new(
          "#{para.name}⁻¹",
          param_space: para.param_space
        ) { |p, a| para.apply(p, a) }  # In full impl, would invert
      end
    end
  end
end
