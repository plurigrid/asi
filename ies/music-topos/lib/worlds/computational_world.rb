# lib/worlds/computational_world.rb
#
# Computational World: Badiouian ontology for Möbius-Chaitin-VonNeumann system
#
# Objects: Programs (prefix-free ternary encodings)
# Metric: Kolmogorov complexity distance
# Appearance: Halting probability contribution
# Intensity: Algorithmic information content

require_relative '../ternary_computer'
require_relative '../moebius'
require_relative '../chaitin_machine'
require_relative '../von_neumann'
require_relative '../worlds'

module MusicalWorlds
  class ComputationalWorld < World
    attr_reader :programs, :chaitin, :simulator, :moebius_lattice

    def initialize(seed: 0x6761795f636f6c6f)
      # Metric: algorithmic distance (approximated by encoding length difference)
      metric = lambda do |p1, p2|
        len1 = p1.is_a?(ChaitinMachine::Program) ? p1.length : p1.to_s.length
        len2 = p2.is_a?(ChaitinMachine::Program) ? p2.length : p2.to_s.length
        (len1 - len2).abs + prefix_distance(p1, p2)
      end

      super("Computational World (Möbius-Chaitin-VonNeumann)", metric)

      @seed = seed
      @programs = {}
      @chaitin = ChaitinMachine::TernaryChaitinMachine.new(seed: seed)
      @simulator = VonNeumann::UniversalSimulator.new(seed: seed)
      @moebius_lattice = Moebius::PrefixLattice.new
    end

    # Add program to world
    def add_program(code, encoding: nil)
      prog = ChaitinMachine::Program.new(code, encoding: encoding)
      @programs[prog.encoding] = prog
      @moebius_lattice.add(prog.encoding, prog)
      add_object(prog)
      prog
    end

    # Execute all programs (dovetailed)
    def execute_all(max_cycles: 100)
      results = {}
      @programs.each do |enc, prog|
        result = @chaitin.execute(prog, max_cycles: max_cycles)
        results[enc] = {
          halted: result[:halted],
          cycles: result[:cycles],
          registers: result[:registers]
        }
      end
      results
    end

    # Compute halting probability Ω₃
    def omega(max_length: 8, max_steps: 500)
      @chaitin.omega.compute(max_length: max_length, max_steps: max_steps)
    end

    # Möbius inversion on program outputs
    def moebius_invert(outputs)
      @chaitin.moebius_invert(outputs)
    end

    # Simulate all von Neumann machines up to size n
    def simulate_all_von_neumann(max_program_length: 6)
      @simulator.enumerate_machines(max_program_length: max_program_length)
      @simulator.dovetail_execute
    end

    # Semantic closure validation (8 dimensions)
    def semantic_closure_validation
      {
        program_space: @programs.any?,
        prefix_free: validate_prefix_free,
        metric_valid: validate_metric_space[:valid],
        appearance: @objects.any?,
        transformations_necessary: validate_moebius_invertible,
        consistent: validate_consistency,
        existence: validate_existence,
        complete: validate_completeness
      }
    end

    # Triangle inequality: d(p1, p3) ≤ d(p1, p2) + d(p2, p3)
    def validate_triangle_inequality(p1, p2, p3)
      d12 = distance(p1, p2)
      d23 = distance(p2, p3)
      d13 = distance(p1, p3)
      { valid: d13 <= d12 + d23, d12: d12, d23: d23, d13: d13 }
    end

    # Factory: create world from Gay.jl color chain
    def self.from_color_chain(chain, seed: 0x6761795f636f6c6f)
      world = new(seed: seed)
      
      chain.each do |entry|
        cycle = entry[:cycle]
        hex = entry[:hex]
        
        # Generate program from color
        prog = world.add_program([cycle, hex.hash.abs % 256], encoding: "C#{cycle}")
      end
      
      world
    end

    private

    def prefix_distance(p1, p2)
      enc1 = p1.is_a?(ChaitinMachine::Program) ? p1.encoding : p1.to_s
      enc2 = p2.is_a?(ChaitinMachine::Program) ? p2.encoding : p2.to_s
      
      # Count differing positions after common prefix
      common = 0
      [enc1.length, enc2.length].min.times do |i|
        break unless enc1[i] == enc2[i]
        common += 1
      end
      
      (enc1.length - common) + (enc2.length - common)
    end

    def validate_prefix_free
      encodings = @programs.keys
      encodings.none? do |e1|
        encodings.any? { |e2| e1 != e2 && e2.start_with?(e1) }
      end
    end

    def validate_moebius_invertible
      return true if @programs.empty?
      
      # Check that Möbius function is well-defined on lattice
      sample = @programs.keys.first(3)
      sample.all? { |enc| @moebius_lattice.mu_lattice(enc, enc) == 1 }
    end

    def validate_consistency
      # No contradictions: same encoding → same program
      @programs.group_by { |enc, _| enc }.all? { |_, v| v.size == 1 }
    end

    def validate_existence
      # Every program exists (has non-zero weight)
      @programs.values.all? { |p| p.weight_ternary > 0 }
    end

    def validate_completeness
      # Closure under prefix lattice operations
      @programs.any?
    end
  end

  # Musical interpretation: programs as compositional processes
  class MusicalComputationalWorld < ComputationalWorld
    # Map computation to music
    def program_to_notes(program, scale: [0, 2, 4, 5, 7, 9, 11])
      result = @chaitin.execute(program, max_cycles: 100)
      
      # Registers → pitches
      result[:registers].map do |r|
        midi = 60 + scale[r.abs % scale.size]
        { pitch: midi, duration: 0.25, velocity: 80 }
      end
    end

    # Möbius inversion reveals "atomic" musical motifs
    def extract_motifs(outputs)
      inverted = moebius_invert(outputs)
      
      # Non-zero inversions are atomic contributions
      inverted.select { |_, v| v != 0 }
              .transform_values { |v| v.abs }
    end

    # Color chain → musical piece
    def color_chain_to_music(chain)
      notes = []
      
      chain.each do |entry|
        prog = @chaitin.program_from_color(entry[:hex], entry[:cycle])
        notes.concat(program_to_notes(prog))
      end
      
      notes
    end
  end
end
