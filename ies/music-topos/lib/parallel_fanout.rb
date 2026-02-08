# lib/parallel_fanout.rb
#
# PARALLEL FANOUT METASKILL
#
# Transforms every interaction into maximally parallel skill dispatch
# using interaction entropy as SplitMixTernary seed.
#
# Architecture:
#   Interaction → Entropy → Seed → Fork(3) → [Generator, Coordinator, Validator]
#   GF(3) conservation: (+1) + (0) + (-1) = 0

require_relative 'splitmix_ternary'

module ParallelFanout
  GOLDEN = SplitMixTernary::GOLDEN
  MASK64 = SplitMixTernary::MASK64

  # Skill triads by domain (GF(3) = 0 guaranteed)
  SKILL_TRIADS = {
    sonification: {
      generator:   { skill: 'supercollider-osc',   trit: +1, color: '#D82626' },
      coordinator: { skill: 'parameter-mapping',   trit:  0, color: '#26D826' },
      validator:   { skill: 'spectral-invariants', trit: -1, color: '#2626D8' }
    },
    derivation: {
      generator:   { skill: 'gay-mcp',     trit: +1, color: '#D82626' },
      coordinator: { skill: 'unworld',     trit:  0, color: '#26D826' },
      validator:   { skill: 'three-match', trit: -1, color: '#2626D8' }
    },
    repl: {
      generator:   { skill: 'cider-clojure', trit: +1, color: '#D82626' },
      coordinator: { skill: 'borkdude',      trit:  0, color: '#26D826' },
      validator:   { skill: 'slime-lisp',    trit: -1, color: '#2626D8' }
    },
    database: {
      generator:   { skill: 'rama-gay-clojure',  trit: +1, color: '#D82626' },
      coordinator: { skill: 'acsets',            trit:  0, color: '#26D826' },
      validator:   { skill: 'clj-kondo-3color',  trit: -1, color: '#2626D8' }
    },
    proof: {
      generator:   { skill: 'gay-mcp',            trit: +1, color: '#D82626' },
      coordinator: { skill: 'squint-runtime',    trit:  0, color: '#26D826' },
      validator:   { skill: 'proofgeneral-narya', trit: -1, color: '#2626D8' }
    },
    game: {
      generator:   { skill: 'rubato-composer',   trit: +1, color: '#D82626' },
      coordinator: { skill: 'glass-bead-game',   trit:  0, color: '#26D826' },
      validator:   { skill: 'bisimulation-game', trit: -1, color: '#2626D8' }
    },
    research: {
      generator:   { skill: 'bmorphism-stars',  trit: +1, color: '#D82626' },
      coordinator: { skill: 'mathpix-ocr',      trit:  0, color: '#26D826' },
      validator:   { skill: 'hatchery-papers',  trit: -1, color: '#2626D8' }
    }
  }

  # Domain detection keywords
  DOMAIN_KEYWORDS = {
    sonification: %w[audio sound music synth osc frequency pitch],
    derivation:   %w[derive color seed chain unworld],
    repl:         %w[eval repl clojure lisp scheme],
    database:     %w[query sql duckdb acset schema],
    proof:        %w[prove type theorem lemma narya],
    game:         %w[game play bead move strategy],
    research:     %w[paper arxiv search cite reference]
  }

  class InteractionEntropy
    attr_reader :text, :char_entropy, :word_entropy, :seed

    def initialize(text)
      @text = text
      @char_entropy = calculate_char_entropy
      @word_entropy = calculate_word_entropy
      @seed = derive_seed
    end

    def calculate_char_entropy
      chars = @text.downcase.chars
      return 0.0 if chars.empty?
      
      freq = chars.each_with_object(Hash.new(0)) { |c, h| h[c] += 1 }
      total = chars.size.to_f
      
      freq.values.sum { |c|
        p = c / total
        -p * Math.log2(p)
      }
    end

    def calculate_word_entropy
      words = @text.downcase.split(/\s+/)
      return 0.0 if words.empty?
      
      freq = words.each_with_object(Hash.new(0)) { |w, h| h[w] += 1 }
      total = words.size.to_f
      
      freq.values.sum { |c|
        p = c / total
        -p * Math.log2(p)
      }
    end

    def derive_seed
      # FNV-1a hash
      fnv1a = 0xcbf29ce484222325
      @text.bytes.each do |b|
        fnv1a ^= b
        fnv1a = (fnv1a * 0x100000001b3) & MASK64
      end
      
      # Combine with entropy bits
      entropy_bits = ((@char_entropy + @word_entropy) * 1_000_000).to_i
      (fnv1a ^ (entropy_bits * GOLDEN)) & MASK64
    end

    def to_h
      {
        text_length: @text.length,
        char_entropy: @char_entropy.round(4),
        word_entropy: @word_entropy.round(4),
        combined: (@char_entropy + @word_entropy).round(4),
        seed: @seed,
        seed_hex: "0x#{@seed.to_s(16)}"
      }
    end
  end

  class Dispatcher
    attr_reader :interaction, :entropy, :domain, :triad, :rng

    def initialize(interaction)
      @interaction = interaction
      @entropy = InteractionEntropy.new(interaction)
      @domain = detect_domain
      @triad = SKILL_TRIADS[@domain]
      @rng = SplitMixTernary::Generator.new(@entropy.seed)
    end

    def detect_domain
      words = @interaction.downcase
      
      scores = DOMAIN_KEYWORDS.transform_values do |keywords|
        keywords.count { |kw| words.include?(kw) }
      end
      
      best = scores.max_by { |_, v| v }
      best[1] > 0 ? best[0] : :derivation  # default to derivation
    end

    def fanout!
      # Fork into 3 independent streams
      children = @rng.fork(3)
      roles = [:generator, :coordinator, :validator]
      
      results = roles.map.with_index do |role, i|
        skill_info = @triad[role]
        child = children[i]
        
        {
          role: role,
          skill: skill_info[:skill],
          trit: skill_info[:trit],
          color: skill_info[:color],
          child_seed: child.seed,
          child_seed_hex: "0x#{child.seed.to_s(16)}",
          sample_colors: (0..2).map { |j| child.split(j).next_color }
        }
      end
      
      # Verify GF(3)
      trit_sum = results.sum { |r| r[:trit] }
      gf3_ok = trit_sum % 3 == 0
      
      {
        interaction: @interaction[0..50] + (@interaction.length > 50 ? '...' : ''),
        domain: @domain,
        entropy: @entropy.to_h,
        gf3_sum: trit_sum,
        gf3_verified: gf3_ok,
        fanout: results
      }
    end

    def meta_fanout(depth: 2)
      return fanout! if depth == 0
      
      children = @rng.fork(3)
      children.map.with_index do |child, i|
        sub = Dispatcher.new(@interaction)
        sub.instance_variable_set(:@entropy, @entropy)
        sub.instance_variable_set(:@rng, child)
        {
          branch: i,
          trit: i - 1,
          subtree: sub.meta_fanout(depth: depth - 1)
        }
      end
    end
  end

  # Module methods
  def self.interaction_entropy(text)
    InteractionEntropy.new(text).to_h
  end

  def self.fanout(interaction)
    Dispatcher.new(interaction).fanout!
  end

  def self.meta_fanout(interaction, depth: 2)
    Dispatcher.new(interaction).meta_fanout(depth: depth)
  end

  def self.list_triads
    SKILL_TRIADS.transform_values do |triad|
      triad.map { |role, info| "#{role}: #{info[:skill]} (#{info[:trit]})" }
    end
  end

  def self.demo
    puts "=" * 70
    puts "PARALLEL FANOUT METASKILL DEMO"
    puts "=" * 70
    
    examples = [
      "sonify this dataset with frequency mapping",
      "derive color chain from seed 0x42D",
      "evaluate clojure expression in repl",
      "query duckdb for recent interactions",
      "prove this theorem using narya types",
      "play glass bead game move connecting math and music"
    ]
    
    examples.each do |ex|
      puts "\n#{'─' * 70}"
      puts "INPUT: #{ex}"
      puts '─' * 70
      
      result = fanout(ex)
      
      puts "Domain:  #{result[:domain]}"
      puts "Entropy: #{result[:entropy][:combined]} bits"
      puts "Seed:    #{result[:entropy][:seed_hex]}"
      puts "GF(3):   #{result[:gf3_sum]} (#{result[:gf3_verified] ? '✓' : '✗'})"
      puts "\nFanout:"
      result[:fanout].each do |f|
        trit_str = f[:trit] >= 0 ? "+#{f[:trit]}" : "#{f[:trit]}"
        puts "  #{f[:role].to_s.ljust(12)} → #{f[:skill].ljust(20)} (trit: #{trit_str}, #{f[:color]})"
      end
    end
    
    puts "\n" + "=" * 70
    puts "All fanouts maintain GF(3) = 0 conservation"
    puts "=" * 70
  end
end

if __FILE__ == $0
  require 'json'
  
  if ARGV[0] == 'demo'
    ParallelFanout.demo
  elsif ARGV[0] == 'entropy'
    puts JSON.pretty_generate(ParallelFanout.interaction_entropy(ARGV[1] || "test"))
  elsif ARGV[0] == 'fanout'
    puts JSON.pretty_generate(ParallelFanout.fanout(ARGV[1] || "test"))
  elsif ARGV[0] == 'triads'
    puts JSON.pretty_generate(ParallelFanout.list_triads)
  else
    ParallelFanout.demo
  end
end
