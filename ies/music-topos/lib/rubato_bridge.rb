# rubato_bridge.rb
# Bridge between Rubato Composer (Mazzola's Topos of Music) and music-topos
#
# Correspondence:
#   Rubato Form      <-> ACSet Schema
#   Rubato Denotator <-> ACSet Instance
#   Rubato Morphism  <-> ACSet Homomorphism
#
# Scheme primitives from RubatoPrimitives.java:
#   form?, denotator?, get-form, get-denotator, type-of, name-of, make-denotator

require_relative 'gay_neverending' rescue nil

module RubatoBridge
  # Form types from Form.java (line 423-427)
  FORM_TYPES = {
    simple:  0,  # Base types (pitch, duration, onset)
    limit:   1,  # Categorical limits (product types)
    colimit: 2,  # Categorical colimits (sum types)
    power:   3,  # Power sets
    list:    4   # Sequence types
  }.freeze

  # Mazzola's performance formula (Vol. II)
  # Performance = Score x Tempo x Dynamics x Articulation
  module Performance
    # Tempo: R+ -> R+ (time deformation)
    # Rubato = bound rubato + free rubato (Chopin rubato)
    # φ₂ = rubato amplitude from Mazzola Vol. II
    def self.rubato(onset, tempo_curve, rubato_amplitude: 0.1, period: 2.0)
      base_tempo = tempo_curve.call(onset)
      # Use golden ratio phase for more musical variation
      phase = onset * Math::PI * 2 / period + 0.618
      deviation = rubato_amplitude * Math.sin(phase)
      base_tempo * (1.0 + deviation)
    end

    # Dynamics: R -> [0,1] (amplitude envelope)
    def self.dynamics(onset, velocity, envelope: :linear)
      case envelope
      when :linear then velocity / 127.0
      when :logarithmic then Math.log(velocity + 1) / Math.log(128)
      when :exponential then (Math.exp(velocity / 127.0) - 1) / (Math::E - 1)
      else velocity / 127.0
      end
    end

    # Articulation: [0,1] (attack/release shaping)
    def self.articulation(duration, articulation_ratio: 0.9)
      duration * articulation_ratio
    end
  end

  # Form: Abstract base for musical types (corresponds to ACSet Schema)
  class Form
    attr_reader :name, :type, :identifier, :coordinate_forms

    def initialize(name:, type:, identifier: nil, coordinate_forms: [])
      @name = name
      @type = FORM_TYPES[type] || type
      @identifier = identifier
      @coordinate_forms = coordinate_forms
    end

    def type_string
      FORM_TYPES.key(@type) || :unknown
    end

    def form_count
      @coordinate_forms.size
    end

    # Convert to ACSet schema representation
    def to_acset_schema
      {
        name: @name,
        objects: coordinate_forms.map(&:name),
        morphisms: [],  # Would be filled by Form structure
        type: type_string
      }
    end

    def to_s
      "#<Form:#{@name} type=#{type_string} coords=#{form_count}>"
    end
  end

  # Denotator: Musical object instance (corresponds to ACSet Instance)
  class Denotator
    attr_reader :name, :form, :coordinate, :frame_coordinate

    def initialize(name:, form:, coordinate: nil, frame_coordinate: nil)
      @name = name
      @form = form
      @coordinate = coordinate
      @frame_coordinate = frame_coordinate || coordinate
    end

    # Convert to ACSet instance representation
    def to_acset_instance
      {
        name: @name,
        form: @form.name,
        data: @coordinate
      }
    end

    def to_s
      "#<Denotator:#{@name} form=#{@form.name}>"
    end
  end

  # SimpleDenotator: Base musical elements (pitch, duration, onset)
  class SimpleDenotator < Denotator
    attr_reader :value

    def initialize(name:, form:, value:)
      super(name: name, form: form)
      @value = value
    end

    def to_sonic_pi
      case @form.name
      when 'Pitch' then { note: @value }
      when 'Duration' then { sustain: @value }
      when 'Onset' then { at: @value }
      when 'Velocity' then { amp: @value / 127.0 }
      else { @form.name.downcase.to_sym => @value }
      end
    end

    def to_s
      "#<SimpleDenotator:#{@name} #{@form.name}=#{@value}>"
    end
  end

  # LimitDenotator: Product type (Note = Pitch x Duration x Onset)
  class LimitDenotator < Denotator
    attr_reader :factors

    def initialize(name:, form:, factors:)
      super(name: name, form: form)
      @factors = factors  # Array of Denotators
    end

    def factor_count
      @factors.size
    end

    def [](index)
      @factors[index]
    end

    def to_sonic_pi
      @factors.each_with_object({}) do |factor, hash|
        hash.merge!(factor.to_sonic_pi)
      end
    end

    def to_s
      "#<LimitDenotator:#{@name} factors=#{factor_count}>"
    end
  end

  # ListDenotator: Sequence of denotators (Score = List of Notes)
  class ListDenotator < Denotator
    attr_reader :elements

    def initialize(name:, form:, elements:)
      super(name: name, form: form)
      @elements = elements
    end

    def size
      @elements.size
    end

    def each(&block)
      @elements.each(&block)
    end

    def to_sonic_pi
      @elements.map(&:to_sonic_pi)
    end

    def to_s
      "#<ListDenotator:#{@name} count=#{size}>"
    end
  end

  # Repository: Form and Denotator storage (mirrors Rubato's Repository.java)
  class Repository
    def initialize
      @forms = {}
      @denotators = {}
      register_builtin_forms!
    end

    def register_form(form)
      @forms[form.name] = form
    end

    def register_denotator(denotator)
      @denotators[denotator.name] = denotator
    end

    def get_form(name)
      @forms[name]
    end

    def get_denotator(name)
      @denotators[name]
    end

    def all_forms
      @forms.values
    end

    def all_denotators
      @denotators.values
    end

    private

    def register_builtin_forms!
      # Simple forms (base types)
      @forms['Pitch'] = Form.new(name: 'Pitch', type: :simple)
      @forms['Duration'] = Form.new(name: 'Duration', type: :simple)
      @forms['Onset'] = Form.new(name: 'Onset', type: :simple)
      @forms['Velocity'] = Form.new(name: 'Velocity', type: :simple)

      # Limit form: Note = Pitch x Duration x Onset x Velocity
      @forms['Note'] = Form.new(
        name: 'Note',
        type: :limit,
        coordinate_forms: [@forms['Pitch'], @forms['Duration'], @forms['Onset'], @forms['Velocity']]
      )

      # List form: Score = List(Note)
      @forms['Score'] = Form.new(
        name: 'Score',
        type: :list,
        coordinate_forms: [@forms['Note']]
      )
    end
  end

  # SchemeInterpreter: Minimal Rubato Scheme dialect
  # Implements primitives from RubatoPrimitives.java
  class SchemeInterpreter
    def initialize(repository = Repository.new)
      @repo = repository
      @env = {}
    end

    def eval(expr)
      case expr
      when Array
        eval_list(expr)
      when Symbol
        @env[expr] || @repo.get_form(expr.to_s) || @repo.get_denotator(expr.to_s)
      else
        expr
      end
    end

    private

    def eval_list(list)
      return nil if list.empty?

      op = list[0]
      args = list[1..]

      case op
      when :'form?'
        eval(args[0]).is_a?(Form)
      when :'denotator?'
        eval(args[0]).is_a?(Denotator)
      when :'get-form'
        @repo.get_form(eval(args[0]).to_s)
      when :'get-denotator'
        @repo.get_denotator(eval(args[0]).to_s)
      when :'type-of'
        obj = eval(args[0])
        obj.respond_to?(:type_string) ? obj.type_string : :unknown
      when :'name-of'
        eval(args[0]).name
      when :'form-of'
        eval(args[0]).form
      when :'make-denotator'
        make_denotator(args)
      when :define
        @env[args[0]] = eval(args[1])
      else
        raise "Unknown primitive: #{op}"
      end
    end

    def make_denotator(args)
      name = eval(args[0]).to_s
      form = @repo.get_form(eval(args[1]).to_s)
      value = eval(args[2])

      case form.type_string
      when :simple
        SimpleDenotator.new(name: name, form: form, value: value)
      when :limit
        LimitDenotator.new(name: name, form: form, factors: value)
      when :list
        ListDenotator.new(name: name, form: form, elements: value)
      else
        Denotator.new(name: name, form: form, coordinate: value)
      end
    end
  end

  # SonicPiBridge: Convert Rubato denotators to Sonic Pi OSC
  class SonicPiBridge
    OSC_PORT = 4560

    def initialize(host: 'localhost', port: OSC_PORT)
      @host = host
      @port = port
    end

    def play_denotator(denotator)
      case denotator
      when SimpleDenotator
        play_simple(denotator)
      when LimitDenotator
        play_note(denotator)
      when ListDenotator
        play_score(denotator)
      end
    end

    def play_score(score)
      score.each do |note|
        play_note(note)
      end
    end

    def play_note(note)
      params = note.to_sonic_pi
      send_osc('/trigger/synth', params[:note] || 60, params[:sustain] || 1, params[:amp] || 0.5)
    end

    def play_simple(simple)
      send_osc('/trigger/synth', simple.value, 1, 0.5)
    end

    private

    def send_osc(path, *args)
      # In production, use osc-ruby gem
      puts "OSC: #{path} #{args.inspect}"
    end
  end

  # ColorGuided: Gay.jl integration for color-guided composition
  module ColorGuided
    GOLDEN_ANGLE = 137.50776405003785  # degrees

    def self.color_at(seed, index)
      # SplitMix64 from Gay.jl
      state = seed
      index.times do
        state = splitmix64_next(state)
      end

      value = splitmix64_next(state)
      hue = (value & 0xFFFF) * 360.0 / 65536.0
      sat = 0.7
      light = 0.55

      { h: hue, s: sat, l: light, hex: hsl_to_hex(hue, sat, light) }
    end

    def self.pitch_from_color(color)
      # Map hue to pitch (0-360 -> 36-96 MIDI range)
      36 + (color[:h] / 360.0 * 60).round
    end

    def self.duration_from_color(color)
      # Map saturation to duration (0.25-2.0 beats)
      0.25 + color[:s] * 1.75
    end

    private

    def self.splitmix64_next(state)
      z = (state + 0x9e3779b97f4a7c15) & 0xFFFFFFFFFFFFFFFF
      z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & 0xFFFFFFFFFFFFFFFF
      z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & 0xFFFFFFFFFFFFFFFF
      z ^ (z >> 31)
    end

    def self.hsl_to_hex(h, s, l)
      c = (1 - (2 * l - 1).abs) * s
      x = c * (1 - ((h / 60.0) % 2 - 1).abs)
      m = l - c / 2.0

      r, g, b = case (h / 60).floor % 6
                when 0 then [c, x, 0]
                when 1 then [x, c, 0]
                when 2 then [0, c, x]
                when 3 then [0, x, c]
                when 4 then [x, 0, c]
                when 5 then [c, 0, x]
                end

      "#%02X%02X%02X" % [(r + m) * 255, (g + m) * 255, (b + m) * 255]
    end
  end

  # Demo: Create a score using Rubato concepts
  def self.demo(seed: 1069, n_notes: 8)
    puts "RUBATO BRIDGE DEMO"
    puts "  Mazzola's Topos of Music -> Sonic Pi"
    puts "  Seed: #{seed} (color-guided composition)"
    puts ""

    repo = Repository.new

    # Show registered forms
    puts "Registered Forms:"
    repo.all_forms.each do |form|
      puts "  #{form}"
    end
    puts ""

    # Create color-guided notes
    puts "Creating #{n_notes} notes via Gay.jl colors:"
    notes = n_notes.times.map do |i|
      color = ColorGuided.color_at(seed, i)
      pitch = ColorGuided.pitch_from_color(color)
      duration = ColorGuided.duration_from_color(color)

      # Create Rubato-style denotators
      pitch_d = SimpleDenotator.new(
        name: "p#{i}",
        form: repo.get_form('Pitch'),
        value: pitch
      )
      duration_d = SimpleDenotator.new(
        name: "d#{i}",
        form: repo.get_form('Duration'),
        value: duration
      )
      onset_d = SimpleDenotator.new(
        name: "o#{i}",
        form: repo.get_form('Onset'),
        value: i * 0.5
      )
      velocity_d = SimpleDenotator.new(
        name: "v#{i}",
        form: repo.get_form('Velocity'),
        value: 80
      )

      note = LimitDenotator.new(
        name: "note#{i}",
        form: repo.get_form('Note'),
        factors: [pitch_d, duration_d, onset_d, velocity_d]
      )

      puts "  #{i}: #{color[:hex]} -> pitch=#{pitch} dur=#{duration.round(2)}"
      note
    end

    # Create score
    score = ListDenotator.new(
      name: "ColorScore",
      form: repo.get_form('Score'),
      elements: notes
    )

    puts ""
    puts "Score created: #{score}"
    puts ""

    # Export to Sonic Pi format
    puts "Sonic Pi export:"
    score.to_sonic_pi.each_with_index do |params, i|
      puts "  play #{params[:note]}, sustain: #{params[:sustain].round(2)}, amp: #{(params[:amp] || 0.6).round(2)}"
    end

    score
  end
end

# Run demo if executed directly
if __FILE__ == $0
  RubatoBridge.demo
end
