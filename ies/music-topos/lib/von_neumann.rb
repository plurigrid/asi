# lib/von_neumann.rb
#
# Von Neumann Machine Simulator
#
# The Chaitin machine simulates EVERY von Neumann machine by:
# 1. Enumerating all possible programs (Gödel numbering)
# 2. Dovetailed execution (fair scheduling)
# 3. Ternary state space (3^n configurations)
#
# Von Neumann architecture:
# - Stored program (code = data)
# - Sequential fetch-decode-execute
# - Memory-mapped I/O

require_relative 'ternary_computer'
require_relative 'chaitin_machine'

module VonNeumann
  # Von Neumann machine state
  class MachineState
    attr_accessor :memory, :pc, :accumulator, :flags, :halted

    def initialize(memory_size: 256)
      @memory = Array.new(memory_size, 0)
      @pc = 0
      @accumulator = 0
      @flags = { zero: false, negative: false, overflow: false }
      @halted = false
    end

    def dup
      copy = MachineState.new(memory_size: @memory.size)
      copy.memory = @memory.dup
      copy.pc = @pc
      copy.accumulator = @accumulator
      copy.flags = @flags.dup
      copy.halted = @halted
      copy
    end

    def to_godel
      # Gödel number: encode state as single integer
      # Use prime factorization: 2^pc × 3^acc × 5^flags × Π p_i^{mem[i]}
      primes = Prime.first(@memory.size + 10)
      n = (primes[0] ** @pc) * (primes[1] ** (@accumulator.abs + 128))
      @memory.each_with_index { |m, i| n *= primes[i + 3] ** (m.abs % 128) }
      n
    end

    def hash; [memory, pc, accumulator, flags, halted].hash; end
    def ==(other); hash == other.hash; end
  end

  # Prime number generator (for Gödel numbering)
  module Prime
    def self.first(n)
      primes = []
      candidate = 2
      while primes.size < n
        primes << candidate if prime?(candidate)
        candidate += 1
      end
      primes
    end

    def self.prime?(n)
      return false if n < 2
      return true if n == 2
      return false if n.even?
      (3..Math.sqrt(n).to_i).step(2).none? { |d| (n % d).zero? }
    end
  end

  # Simple von Neumann instruction set
  # Opcode (4 bits) | Operand (12 bits) = 16-bit instruction
  class InstructionSet
    OPCODES = {
      0x0 => :NOP,   # No operation
      0x1 => :LDA,   # Load accumulator from memory
      0x2 => :STA,   # Store accumulator to memory
      0x3 => :ADD,   # Add memory to accumulator
      0x4 => :SUB,   # Subtract memory from accumulator
      0x5 => :JMP,   # Unconditional jump
      0x6 => :JZ,    # Jump if zero
      0x7 => :JN,    # Jump if negative
      0x8 => :AND,   # Bitwise AND
      0x9 => :OR,    # Bitwise OR
      0xA => :XOR,   # Bitwise XOR
      0xB => :NOT,   # Bitwise NOT
      0xC => :SHL,   # Shift left
      0xD => :SHR,   # Shift right
      0xE => :IN,    # Input
      0xF => :HLT    # Halt
    }.freeze

    def self.decode(word)
      opcode = (word >> 12) & 0xF
      operand = word & 0xFFF
      [OPCODES[opcode] || :NOP, operand]
    end

    def self.encode(opcode, operand)
      op = OPCODES.key(opcode) || 0
      (op << 12) | (operand & 0xFFF)
    end
  end

  # Von Neumann Machine Executor
  class Machine
    attr_reader :state, :history, :cycle_count

    def initialize(memory_size: 256)
      @state = MachineState.new(memory_size: memory_size)
      @history = []
      @cycle_count = 0
      @input_buffer = []
      @output_buffer = []
    end

    def load(program)
      program.each_with_index { |word, i| @state.memory[i] = word if i < @state.memory.size }
      self
    end

    def input(values)
      @input_buffer = values.dup
      self
    end

    def step
      return if @state.halted
      
      @history << @state.dup
      @cycle_count += 1

      # Fetch
      instr = @state.memory[@state.pc % @state.memory.size]
      
      # Decode
      opcode, operand = InstructionSet.decode(instr)
      
      # Execute
      execute(opcode, operand)
      
      # Increment PC (unless jump)
      @state.pc += 1 unless [:JMP, :JZ, :JN, :HLT].include?(opcode)
    end

    def run(max_cycles: 10_000)
      step until @state.halted || @cycle_count >= max_cycles
      {
        halted: @state.halted,
        cycles: @cycle_count,
        accumulator: @state.accumulator,
        output: @output_buffer
      }
    end

    def output; @output_buffer; end

    private

    def execute(opcode, operand)
      addr = operand % @state.memory.size
      
      case opcode
      when :NOP then nil
      when :LDA then @state.accumulator = @state.memory[addr]
      when :STA then @state.memory[addr] = @state.accumulator
      when :ADD
        @state.accumulator += @state.memory[addr]
        update_flags
      when :SUB
        @state.accumulator -= @state.memory[addr]
        update_flags
      when :JMP then @state.pc = addr - 1  # -1 because we add 1 after
      when :JZ  then @state.pc = addr - 1 if @state.flags[:zero]
      when :JN  then @state.pc = addr - 1 if @state.flags[:negative]
      when :AND then @state.accumulator &= @state.memory[addr]
      when :OR  then @state.accumulator |= @state.memory[addr]
      when :XOR then @state.accumulator ^= @state.memory[addr]
      when :NOT then @state.accumulator = ~@state.accumulator
      when :SHL then @state.accumulator <<= (operand & 0xF)
      when :SHR then @state.accumulator >>= (operand & 0xF)
      when :IN  then @state.accumulator = @input_buffer.shift || 0
      when :HLT
        @output_buffer << @state.accumulator
        @state.halted = true
      end
    end

    def update_flags
      @state.flags[:zero] = @state.accumulator == 0
      @state.flags[:negative] = @state.accumulator < 0
      @state.flags[:overflow] = @state.accumulator.abs > 0x7FFF
    end
  end

  # Universal Simulator: Chaitin machine simulating all von Neumann machines
  class UniversalSimulator
    attr_reader :machines, :results

    def initialize(seed: 0x6761795f636f6c6f)
      @seed = seed
      @rng = Random.new(seed)
      @machines = {}
      @results = {}
      @chaitin = ChaitinMachine::TernaryChaitinMachine.new(seed: seed)
    end

    # Generate all von Neumann machines up to program length n
    def enumerate_machines(max_program_length: 8, base: 3)
      count = base ** max_program_length
      
      (0...count).each do |godel_num|
        # Convert Gödel number to program
        program = godel_to_program(godel_num, max_program_length, base)
        machine = Machine.new
        machine.load(program)
        
        @machines[godel_num] = {
          program: program,
          machine: machine,
          encoding: Moebius::TernaryEncoder.encode(godel_num)
        }
      end

      @machines.size
    end

    # Dovetailed execution of all machines
    def dovetail_execute(max_steps_per_round: 10, max_rounds: 100)
      active = @machines.keys.dup
      round = 0

      while active.any? && round < max_rounds
        round += 1
        
        active.reject! do |godel_num|
          machine = @machines[godel_num][:machine]
          max_steps_per_round.times { machine.step unless machine.state.halted }
          
          if machine.state.halted
            @results[godel_num] = {
              halted: true,
              cycles: machine.cycle_count,
              output: machine.output,
              round: round
            }
            true
          else
            false
          end
        end
      end

      # Mark non-halting machines
      active.each do |godel_num|
        @results[godel_num] = {
          halted: false,
          cycles: @machines[godel_num][:machine].cycle_count,
          output: [],
          round: round
        }
      end

      {
        total: @machines.size,
        halted: @results.count { |_, r| r[:halted] },
        non_halting: @results.count { |_, r| !r[:halted] },
        rounds: round
      }
    end

    # Apply Möbius inversion to program outputs
    def moebius_invert_outputs
      outputs = @results.transform_keys { |k| @machines[k][:encoding] }
                        .transform_values { |r| r[:output].first || 0 }
      
      @chaitin.moebius_invert(outputs)
    end

    # Find machines producing specific output
    def find_machines_producing(target)
      @results.select { |_, r| r[:halted] && r[:output].include?(target) }
              .transform_keys { |k| @machines[k][:encoding] }
    end

    private

    def godel_to_program(n, length, base)
      program = []
      length.times do
        program << (n % base)
        n /= base
      end
      
      # Convert to von Neumann instructions
      program.each_slice(2).map do |op, arg|
        InstructionSet.encode(InstructionSet::OPCODES.keys[op.to_i % 16], arg.to_i)
      end
    end
  end

  # Self-replicating von Neumann constructor (for completeness)
  class SelfReplicator
    attr_reader :tape, :generations

    def initialize(seed_program)
      @tape = seed_program.dup
      @generations = [seed_program.dup]
    end

    # Quine-like self-replication
    def replicate
      # Read own code
      own_code = @tape.dup
      
      # Append copy to tape
      @tape.concat(own_code)
      @generations << own_code
      
      @generations.size
    end

    # Universal constructor: build any machine from blueprint
    def construct(blueprint)
      Machine.new.load(blueprint)
    end
  end
end
