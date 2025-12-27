# lib/ternary_computer.rb
#
# Balanced Ternary Computer: {T, 0, 1} = {-1, 0, +1}
# More efficient than binary for certain operations
# Natural representation for comparisons: <, =, >

module TernaryComputer
  # Balanced ternary trit: -1 (T), 0, +1 (1)
  class Trit
    SYMBOLS = { -1 => 'T', 0 => '0', 1 => '1' }.freeze
    VALUES = { 'T' => -1, '0' => 0, '1' => 1 }.freeze

    attr_reader :value

    def initialize(v)
      @value = case v
               when Integer then v <=> 0  # normalize to {-1, 0, 1}
               when String then VALUES[v] || 0
               else 0
               end
    end

    def to_s; SYMBOLS[@value]; end
    def -@; Trit.new(-@value); end
    def +(other); Trit.new(@value + other.value); end
    def *(other); Trit.new(@value * other.value); end
    def ==(other); @value == other.value; end
  end

  # Balanced ternary word (array of trits)
  class Word
    attr_reader :trits, :width

    def initialize(value, width: 12)
      @width = width
      @trits = case value
               when Integer then int_to_trits(value, width)
               when Array then value.map { |t| t.is_a?(Trit) ? t : Trit.new(t) }
               when String then value.chars.map { |c| Trit.new(c) }
               else [Trit.new(0)] * width
               end
      @trits = @trits.take(width).fill(Trit.new(0), @trits.size...width)
    end

    def to_i
      @trits.each_with_index.sum { |t, i| t.value * (3 ** i) }
    end

    def to_s
      @trits.reverse.map(&:to_s).join
    end

    def [](i); @trits[i]; end
    def []=(i, v); @trits[i] = v.is_a?(Trit) ? v : Trit.new(v); end

    def +(other)
      carry = 0
      result = @trits.zip(other.trits).map do |a, b|
        sum = a.value + b.value + carry
        # Balanced ternary normalization
        if sum > 1
          carry = 1
          Trit.new(sum - 3)
        elsif sum < -1
          carry = -1
          Trit.new(sum + 3)
        else
          carry = 0
          Trit.new(sum)
        end
      end
      Word.new(result, width: @width)
    end

    def -@
      Word.new(@trits.map { |t| -t }, width: @width)
    end

    def -(other); self + (-other); end

    def *(other)
      result = Word.new(0, width: @width * 2)
      @trits.each_with_index do |t, i|
        partial = other.trits.map { |o| t * o }
        shifted = ([Trit.new(0)] * i) + partial
        result = result + Word.new(shifted, width: @width * 2)
      end
      Word.new(result.trits.take(@width), width: @width)
    end

    def compare(other)
      # Natural ternary comparison: returns Trit
      diff = to_i - other.to_i
      Trit.new(diff <=> 0)
    end

    private

    def int_to_trits(n, width)
      trits = []
      n = n.to_i
      neg = n < 0
      n = n.abs
      width.times do
        rem = n % 3
        n /= 3
        if rem == 2
          rem = -1
          n += 1
        end
        trits << Trit.new(neg ? -rem : rem)
      end
      trits
    end
  end

  # Ternary register machine (3^12 = 531441 addressable words)
  class Machine
    REGISTER_COUNT = 9  # R0-R8 (ternary: TTT to 111)
    MEMORY_SIZE = 729   # 3^6 words

    attr_reader :registers, :memory, :pc, :halted, :cycles

    def initialize
      @registers = Array.new(REGISTER_COUNT) { Word.new(0) }
      @memory = Array.new(MEMORY_SIZE) { Word.new(0) }
      @pc = 0
      @halted = false
      @cycles = 0
    end

    # Instruction format: [op:3][dst:3][src1:3][src2:3]
    # op: TTT=halt, TT0=load, TT1=store, T0T=add, T00=sub, T01=mul,
    #     T1T=cmp, T10=jmp, T11=jz, 0TT=jnz, 0T0=and, 0T1=or, 00T=xor
    OPCODES = {
      'TTT' => :halt, 'TT0' => :load, 'TT1' => :store,
      'T0T' => :add,  'T00' => :sub,  'T01' => :mul,
      'T1T' => :cmp,  'T10' => :jmp,  'T11' => :jz,
      '0TT' => :jnz,  '0T0' => :and,  '0T1' => :or,
      '00T' => :xor,  '000' => :nop,  '001' => :neg,
      '01T' => :shl,  '010' => :shr,  '011' => :mov,
      '1TT' => :inc,  '1T0' => :dec,  '1T1' => :push,
      '10T' => :pop,  '100' => :call, '101' => :ret,
      '11T' => :in,   '110' => :out,  '111' => :syscall
    }.freeze

    def load_program(program)
      program.each_with_index { |word, i| @memory[i] = word if i < MEMORY_SIZE }
    end

    def step
      return if @halted
      @cycles += 1

      instr = @memory[@pc % MEMORY_SIZE]
      op = instr.trits[0..2].map(&:to_s).join
      dst = trit3_to_idx(instr.trits[3..5])
      src1 = trit3_to_idx(instr.trits[6..8])
      src2 = trit3_to_idx(instr.trits[9..11])

      opcode = OPCODES[op] || :nop
      execute(opcode, dst, src1, src2)
      @pc += 1 unless [:jmp, :jz, :jnz, :call, :ret, :halt].include?(opcode)
    end

    def run(max_cycles: 1000)
      step until @halted || @cycles >= max_cycles
      { halted: @halted, cycles: @cycles, registers: @registers.map(&:to_i) }
    end

    private

    def trit3_to_idx(trits)
      (trits[0]&.value.to_i * 9 + trits[1]&.value.to_i * 3 + trits[2]&.value.to_i + 13) % REGISTER_COUNT
    end

    def execute(op, dst, src1, src2)
      case op
      when :halt  then @halted = true
      when :nop   then nil
      when :add   then @registers[dst] = @registers[src1] + @registers[src2]
      when :sub   then @registers[dst] = @registers[src1] - @registers[src2]
      when :mul   then @registers[dst] = @registers[src1] * @registers[src2]
      when :mov   then @registers[dst] = Word.new(@registers[src1].trits.dup)
      when :neg   then @registers[dst] = -@registers[src1]
      when :inc   then @registers[dst] = @registers[dst] + Word.new(1)
      when :dec   then @registers[dst] = @registers[dst] - Word.new(1)
      when :cmp   then @registers[dst] = Word.new(@registers[src1].compare(@registers[src2]).value)
      when :jmp   then @pc = @registers[dst].to_i.abs % MEMORY_SIZE
      when :jz    then @pc = @registers[src1].to_i.abs % MEMORY_SIZE if @registers[dst].to_i == 0
      when :jnz   then @pc = @registers[src1].to_i.abs % MEMORY_SIZE if @registers[dst].to_i != 0
      when :load  then @registers[dst] = @memory[@registers[src1].to_i.abs % MEMORY_SIZE]
      when :store then @memory[@registers[src1].to_i.abs % MEMORY_SIZE] = @registers[dst]
      end
    end
  end
end
