# lib/world_demo_topos.rb
#
# WORLD DEMO TOPOS: Unified Demo Orchestration
#
# Collects all demos across the codebase and runs them as a topos
# of demonstrations with GF(3) conservation and color streams.
#
# Found demos:
#   Ruby:  tritwise_letter_spirit, synadia_broadcast, glass_bead_game,
#          tdx_color_logic, skill_sonification, xoroshiro_3color,
#          maximum_dynamism, bb6_hypercomputation, prediction_market_proofs
#   Julia: rama_acset_parallel, gay_org_multi_remote, unified_verification_bridge,
#          colored_sexp_acset, self_avoiding_expander_tsirelson
#   Elisp: narya/demo, gay-3color-demo
#   Jank:  crdt_sexp_ewig/demo
#   BB:    mcp-tasks/demo

require_relative 'xoroshiro_3color'

module WorldDemoTopos
  # All discovered demos with their metadata
  DEMOS = {
    # Ruby demos
    tritwise: {
      lang: :ruby,
      file: 'tritwise_letter_spirit.rb',
      call: 'TritwiseLetterSpirit.demo',
      trit: -1,
      category: :color
    },
    synadia: {
      lang: :ruby,
      file: 'synadia_broadcast.rb',
      call: 'SynadiaBroadcast.demo',
      trit: 0,
      category: :messaging
    },
    glass_bead: {
      lang: :ruby,
      file: 'glass_bead_game.rb',
      call: 'GlassBeadGame.demo',
      trit: 1,
      category: :game
    },
    tdx_color: {
      lang: :ruby,
      file: 'tdx_color_logic.rb',
      call: 'TDXColorLogic.demo',
      trit: -1,
      category: :type
    },
    skill_sonification: {
      lang: :ruby,
      file: 'skill_sonification.rb',
      call: 'SkillSonification::MatrixFactory.demo',
      trit: 0,
      category: :audio
    },
    xoroshiro_3color: {
      lang: :ruby,
      file: 'xoroshiro_3color.rb',
      call: 'Xoroshiro3Color.demo',
      trit: 1,
      category: :color
    },
    maximum_dynamism: {
      lang: :ruby,
      file: 'maximum_dynamism.rb',
      call: 'MaximumDynamism.maximum_dynamism_demo',
      trit: -1,
      category: :audio
    },
    bb6_hypercomputation: {
      lang: :ruby,
      file: 'bb6_hypercomputation.rb',
      call: 'BB6Hypercomputation.demonstrate!',
      trit: 0,
      category: :computation
    },
    prediction_market: {
      lang: :ruby,
      file: 'prediction_market_proofs.rb',
      call: 'PredictionMarketProofs.demonstrate!',
      trit: 1,
      category: :market
    },
    genesis_chain: {
      lang: :ruby,
      file: 'genesis_chain.rb',
      call: 'GenesisChain.decide!',
      trit: -1,
      category: :chain
    },
    
    # Julia demos
    rama_acset: {
      lang: :julia,
      file: 'rama_acset_parallel.jl',
      call: 'demo_rama_acset()',
      trit: 0,
      category: :acset
    },
    gay_org_multi: {
      lang: :julia,
      file: 'gay_org_multi_remote.jl',
      call: 'demo()',
      trit: 1,
      category: :color
    },
    unified_verification: {
      lang: :julia,
      file: 'unified_verification_bridge.jl',
      call: 'demo()',
      trit: -1,
      category: :verification
    },
    colored_sexp_acset: {
      lang: :julia,
      file: 'colored_sexp_acset.jl',
      call: 'demo()',
      trit: 0,
      category: :acset
    },
    self_avoiding_expander: {
      lang: :julia,
      file: 'self_avoiding_expander_tsirelson.jl',
      call: 'demo()',
      trit: 1,
      category: :graph
    },
    
    # Elisp demos
    narya_bridge: {
      lang: :elisp,
      file: 'narya_observational_bridge.el',
      call: '(narya/demo)',
      trit: -1,
      category: :type
    },
    gay_3color: {
      lang: :elisp,
      file: 'gay.el',
      call: '(gay-3color-demo)',
      trit: 0,
      category: :color
    },
    
    # Babashka demos
    mcp_tasks: {
      lang: :babashka,
      file: 'mcp-tasks.bb',
      call: '(demo 0x42D)',
      trit: 1,
      category: :mcp
    }
  }.freeze
  
  # Group demos by trit for GF(3) conservation
  TRIT_GROUPS = DEMOS.group_by { |_, v| v[:trit] }.freeze
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # DEMO RUNNER
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class DemoRunner
    attr_reader :streams, :results, :history
    
    def initialize(seed = 0x42D)
      @seed = seed
      @streams = Xoroshiro3Color::TripartiteStreams.new(seed)
      @results = {}
      @history = []
    end
    
    # Run a single demo
    def run_demo(name)
      demo = DEMOS[name]
      raise ArgumentError, "Unknown demo: #{name}" unless demo
      
      triplet = @streams.next_triplet
      color = triplet[%i[minus ergodic plus][demo[:trit] + 1]]
      
      result = case demo[:lang]
               when :ruby
                 run_ruby_demo(demo)
               when :julia
                 run_julia_demo(demo)
               when :elisp
                 run_elisp_demo(demo)
               when :babashka
                 run_babashka_demo(demo)
               else
                 { error: "Unknown language: #{demo[:lang]}" }
               end
      
      entry = {
        name: name,
        demo: demo,
        color: color,
        triplet: triplet,
        result: result,
        timestamp: Time.now
      }
      @history << entry
      @results[name] = entry
      entry
    end
    
    # Run demos in GF(3) triplets (one from each trit group)
    def run_triplet
      minus_demos = TRIT_GROUPS[-1]&.keys || []
      ergodic_demos = TRIT_GROUPS[0]&.keys || []
      plus_demos = TRIT_GROUPS[1]&.keys || []
      
      # Pick one from each
      m = minus_demos.sample
      e = ergodic_demos.sample
      p = plus_demos.sample
      
      results = []
      results << run_demo(m) if m
      results << run_demo(e) if e
      results << run_demo(p) if p
      
      {
        demos: results.map { |r| r[:name] },
        gf3_sum: results.sum { |r| r[:demo][:trit] },
        conserved: results.sum { |r| r[:demo][:trit] } % 3 == 0
      }
    end
    
    # Run all demos in a category
    def run_category(category)
      demos = DEMOS.select { |_, v| v[:category] == category }
      demos.keys.map { |name| run_demo(name) }
    end
    
    # Run all Ruby demos (fastest)
    def run_all_ruby
      DEMOS.select { |_, v| v[:lang] == :ruby }.keys.map { |name| run_demo(name) }
    end
    
    private
    
    def run_ruby_demo(demo)
      begin
        require_relative demo[:file].sub('.rb', '')
        output = capture_output { eval(demo[:call]) }
        { success: true, output: output }
      rescue => e
        { success: false, error: e.message }
      end
    end
    
    def run_julia_demo(demo)
      cmd = "julia --project=. -e 'include(\"lib/#{demo[:file]}\")'"
      output = `#{cmd} 2>&1`
      { success: $?.success?, output: output.lines.last(20).join }
    end
    
    def run_elisp_demo(demo)
      cmd = "emacs --batch -l lib/#{demo[:file]} --eval '#{demo[:call]}' 2>&1"
      output = `#{cmd}`
      { success: $?.success?, output: output }
    end
    
    def run_babashka_demo(demo)
      cmd = "bb lib/#{demo[:file]} 2>&1"
      output = `#{cmd}`
      { success: $?.success?, output: output.lines.last(20).join }
    end
    
    def capture_output
      old_stdout = $stdout
      $stdout = StringIO.new
      yield
      $stdout.string
    ensure
      $stdout = old_stdout
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # TOPOS OF DEMOS
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class DemoTopos
    # Morphisms between demos (dependencies/compositions)
    MORPHISMS = {
      [:xoroshiro_3color, :tritwise] => :color_composition,
      [:synadia, :glass_bead] => :game_broadcast,
      [:rama_acset, :colored_sexp_acset] => :acset_coloring,
      [:narya_bridge, :gay_3color] => :elisp_bridge,
      [:genesis_chain, :prediction_market] => :chain_market
    }.freeze
    
    attr_reader :runner
    
    def initialize(seed = 0x42D)
      @runner = DemoRunner.new(seed)
    end
    
    # List all demos
    def objects
      DEMOS.keys
    end
    
    # List all morphisms
    def morphisms
      MORPHISMS
    end
    
    # Compose two demos
    def compose(demo1, demo2)
      morphism = MORPHISMS[[demo1, demo2]]
      raise "No morphism from #{demo1} to #{demo2}" unless morphism
      
      r1 = @runner.run_demo(demo1)
      r2 = @runner.run_demo(demo2)
      
      {
        source: demo1,
        target: demo2,
        morphism: morphism,
        results: [r1, r2],
        gf3_sum: r1[:demo][:trit] + r2[:demo][:trit]
      }
    end
    
    # Terminal object: the world demo that collects all
    def terminal
      :world_demo_topos
    end
    
    # Initial object: the seed
    def initial
      @runner.instance_variable_get(:@seed)
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # WORLD DEMONSTRATION
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.world(seed: 0x42D, mode: :summary)
    puts "╔═══════════════════════════════════════════════════════════════════╗"
    puts "║  WORLD DEMO TOPOS: Unified Demo Orchestration                    ║"
    puts "╚═══════════════════════════════════════════════════════════════════╝"
    puts
    puts "Seed: 0x#{seed.to_s(16)}"
    puts "Total demos: #{DEMOS.size}"
    puts
    
    # Group by language
    by_lang = DEMOS.group_by { |_, v| v[:lang] }
    puts "─── By Language ───"
    by_lang.each do |lang, demos|
      puts "  #{lang}: #{demos.size} demos"
    end
    puts
    
    # Group by category
    by_cat = DEMOS.group_by { |_, v| v[:category] }
    puts "─── By Category ───"
    by_cat.each do |cat, demos|
      puts "  #{cat}: #{demos.map { |k, _| k }.join(', ')}"
    end
    puts
    
    # Group by trit
    puts "─── By Trit (GF(3)) ───"
    [-1, 0, 1].each do |trit|
      demos = DEMOS.select { |_, v| v[:trit] == trit }
      label = case trit
              when -1 then "MINUS (-1)"
              when 0 then "ERGODIC (0)"
              when 1 then "PLUS (+1)"
              end
      puts "  #{label}: #{demos.keys.join(', ')}"
    end
    puts
    
    if mode == :run
      runner = DemoRunner.new(seed)
      
      puts "─── Running GF(3) Triplet ───"
      triplet_result = runner.run_triplet
      puts "  Demos: #{triplet_result[:demos].join(' ⊗ ')}"
      puts "  GF(3) sum: #{triplet_result[:gf3_sum]}"
      puts "  Conserved: #{triplet_result[:conserved] ? '✓' : '✗'}"
      puts
    end
    
    puts "─── Quick Commands ───"
    puts "  just world-demo              # Run this summary"
    puts "  just world-demo-triplet      # Run GF(3) triplet"
    puts "  just world-demo-ruby         # Run all Ruby demos"
    puts "  just world-demo-color        # Run color demos"
    puts
    
    puts "═══════════════════════════════════════════════════════════════════"
    puts "The topos of demos forms a category with #{DEMOS.size} objects"
    puts "and #{DemoTopos::MORPHISMS.size} explicit morphisms."
    puts "═══════════════════════════════════════════════════════════════════"
  end
  
  def self.list
    DEMOS.each do |name, demo|
      trit_sym = case demo[:trit]
                 when -1 then "−"
                 when 0 then "○"
                 when 1 then "+"
                 end
      puts "#{trit_sym} #{name.to_s.ljust(25)} [#{demo[:lang]}] #{demo[:category]}"
    end
  end
  
  def self.run_triplet(seed: 0x42D)
    runner = DemoRunner.new(seed)
    runner.run_triplet
  end
end

if __FILE__ == $0
  WorldDemoTopos.world(mode: ARGV.include?('--run') ? :run : :summary)
end
