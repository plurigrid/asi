# lib/chaitin_machine.rb
#
# Chaitin Universal Prefix-Free Turing Machine
#
# Key properties:
# 1. Prefix-free: no valid program is prefix of another
# 2. Universal: simulates any TM given its encoding
# 3. Ω = Σ 2^{-|p|} for halting programs p (Chaitin's Omega)
#
# This implementation uses ternary (3^{-|p|}) for Ω₃

require_relative 'ternary_computer'
require_relative 'moebius'

module ChaitinMachine
  # Prefix-free program representation
  class Program
    attr_reader :code, :encoding, :length

    def initialize(code, encoding: nil)
      @code = code
      @encoding = encoding || Moebius::TernaryEncoder.encode(code.hash.abs % 1000)
      @length = @encoding.length
    end

    def prefix?(other)
      other.encoding.start_with?(@encoding)
    end

    def weight_binary; 2.0 ** (-@length); end
    def weight_ternary; 3.0 ** (-@length); end

    def to_s; "Program(#{@encoding}, len=#{@length})"; end
  end

  # Universal Ternary Turing Machine
  # Simulates other machines given their Gödel encoding
  class UniversalMachine
    BLANK = 0
    TAPE_SIZE = 1000

    attr_reader :tape, :head, :state, :halted, :steps

    def initialize
      @tape = Array.new(TAPE_SIZE, BLANK)
      @head = TAPE_SIZE / 2
      @state = 0
      @halted = false
      @steps = 0
      @transition_table = {}
    end

    # Load program encoded as transition table
    # Format: [[state, read, write, move, next_state], ...]
    # move: -1 (left), 0 (stay), 1 (right) — ternary!
    def load(transitions)
      @transition_table = {}
      transitions.each do |t|
        state, read, write, move, next_state = t
        @transition_table[[state, read]] = [write, move, next_state]
      end
      self
    end

    # Load from ternary-encoded program
    def load_encoded(program)
      # Decode ternary program to transition table
      code = program.is_a?(Program) ? program.code : program
      transitions = decode_program(code)
      load(transitions)
    end

    def step
      return if @halted
      @steps += 1

      read = @tape[@head] || BLANK
      key = [@state, read]

      unless @transition_table.key?(key)
        @halted = true
        return
      end

      write, move, next_state = @transition_table[key]
      @tape[@head] = write
      @head = (@head + move).clamp(0, TAPE_SIZE - 1)
      @state = next_state

      @halted = true if next_state == -1  # Halt state
    end

    def run(max_steps: 10_000)
      step until @halted || @steps >= max_steps
      { halted: @halted, steps: @steps, output: output }
    end

    def output
      # Non-blank tape content
      left = @tape.index { |t| t != BLANK } || 0
      right = @tape.rindex { |t| t != BLANK } || 0
      @tape[left..right]
    end

    private

    def decode_program(code)
      # Simple encoding: each group of 5 trits is a transition
      return [] if code.nil? || code.empty?
      
      trits = code.is_a?(String) ? code.chars.map { |c| c == 'T' ? -1 : c.to_i } : code
      transitions = []
      
      trits.each_slice(5) do |t|
        next if t.size < 5
        transitions << t.map { |v| v.is_a?(Integer) ? v : (v == 'T' ? -1 : v.to_i) }
      end
      
      transitions
    end
  end

  # Chaitin Omega: halting probability
  class Omega
    attr_reader :programs, :halting, :omega_approx

    def initialize
      @programs = []
      @halting = []
      @omega_approx = 0.0
    end

    # Enumerate programs up to length n, dovetail execution
    def compute(max_length: 10, max_steps: 1000)
      # Generate all prefix-free programs
      codes = Moebius::TernaryEncoder.all_codes(max_length)
      @programs = codes.map.with_index { |enc, i| Program.new(i, encoding: enc) }

      # Dovetail: run each program for increasing step counts
      @halting = []
      @programs.each do |prog|
        machine = UniversalMachine.new
        machine.load_encoded(prog)
        result = machine.run(max_steps: max_steps)
        @halting << prog if result[:halted]
      end

      # Compute Ω₃ approximation
      @omega_approx = @halting.sum(&:weight_ternary)

      {
        programs_tested: @programs.size,
        halting_count: @halting.size,
        omega_ternary: @omega_approx,
        omega_bits: -Math.log2(@omega_approx).round(4)
      }
    end

    # Kolmogorov complexity approximation
    # K(x) = min { |p| : U(p) = x }
    def kolmogorov(target_output, max_length: 12, max_steps: 500)
      codes = Moebius::TernaryEncoder.all_codes(max_length)
      
      codes.each do |enc|
        prog = Program.new(enc.hash, encoding: enc)
        machine = UniversalMachine.new
        machine.load_encoded(prog)
        result = machine.run(max_steps: max_steps)
        
        if result[:halted] && result[:output] == target_output
          return { complexity: prog.length, program: prog }
        end
      end

      { complexity: Float::INFINITY, program: nil }
    end
  end

  # Ternary Chaitin Machine: combines all components
  class TernaryChaitinMachine
    attr_reader :omega, :lattice, :ternary_machine

    def initialize(seed: 0x6761795f636f6c6f)  # "gay_colo"
      @omega = Omega.new
      @lattice = Moebius::PrefixLattice.new
      @ternary_machine = TernaryComputer::Machine.new
      @seed = seed
      @rng = Random.new(seed)
    end

    # Register program in prefix lattice
    def register_program(code)
      prog = Program.new(code)
      @lattice.add(prog.encoding, prog)
      prog
    end

    # Run program on ternary machine
    def execute(program, max_cycles: 1000)
      # Convert to ternary machine code
      words = program_to_words(program)
      @ternary_machine = TernaryComputer::Machine.new
      @ternary_machine.load_program(words)
      @ternary_machine.run(max_cycles: max_cycles)
    end

    # Möbius inversion on program outputs
    def moebius_invert(outputs)
      # outputs: encoding → value
      inverted = {}
      outputs.keys.each do |enc|
        inverted[enc] = @lattice.invert_prefix(outputs, enc)
      end
      inverted
    end

    # Color-driven program generation (from Gay.jl chain)
    def program_from_color(hex, cycle)
      # Extract LCH from hex, map to program parameters
      rgb = hex_to_rgb(hex)
      hue_word = TernaryComputer::Word.new((rgb[0] * 3).round)
      sat_word = TernaryComputer::Word.new((rgb[1] * 3).round)
      lit_word = TernaryComputer::Word.new((rgb[2] * 3).round)
      
      # Generate deterministic program from color
      Program.new([hue_word.to_i, sat_word.to_i, lit_word.to_i, cycle])
    end

    private

    def program_to_words(program)
      code = program.is_a?(Program) ? program.code : program
      return [] unless code.is_a?(Array)
      
      code.map { |v| TernaryComputer::Word.new(v.to_i) }
    end

    def hex_to_rgb(hex)
      hex = hex.gsub('#', '')
      [hex[0..1], hex[2..3], hex[4..5]].map { |c| c.to_i(16) / 255.0 }
    end
  end
end
