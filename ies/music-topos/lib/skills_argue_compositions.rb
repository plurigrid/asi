# lib/skills_argue_compositions.rb
#
# SKILLS ARGUE: Which 3 Compositions?
#
# GF(3) Conservation Triad:
#   rubato-composer (+1) ⊗ glass-bead-game (0) ⊗ bisimulation-game (-1) = 0 ✓
#
# Each skill argues from its perspective:
#   Generator (+1): Proposes compositions via Mazzola's Forms
#   Coordinator (0): Evaluates world-hopping connections
#   Validator (-1): Verifies bisimulation equivalence
#
# The 3 compositions selected must themselves form a GF(3) = 0 triad.

require_relative 'splitmix_ternary'
require_relative 'self_avoiding_colored_walk'

module SkillsArgueCompositions
  
  # ═══════════════════════════════════════════════════════════════════════════
  # COMPOSITION CANDIDATES (from rubato-composer's Mazzola Forms)
  # ═══════════════════════════════════════════════════════════════════════════
  
  COMPOSITIONS = {
    # GENERATOR class (+1): Expansive, generative works
    bach_goldberg: {
      name: "Bach: Goldberg Variations",
      form: :limit,  # Product type (LimitForm)
      trit: +1,
      domain: :counterpoint,
      morphisms: [:canon, :inversion, :augmentation],
      denotator: { voices: 4, variations: 30, aria: true }
    },
    ligeti_etudes: {
      name: "Ligeti: Piano Études",
      form: :colimit,  # Sum type (ColimitForm)
      trit: +1,
      domain: :rhythm,
      morphisms: [:polyrhythm, :metric_modulation, :dislocated_counterpoint],
      denotator: { books: 3, etudes: 18, techniques: [:blocked_keys, :fanfares] }
    },
    xenakis_metastasis: {
      name: "Xenakis: Metastaseis",
      form: :list,  # Sequence type (ListForm)
      trit: +1,
      domain: :stochastic,
      morphisms: [:glissando_mass, :probability_distribution, :sieve],
      denotator: { duration_min: 7, instruments: 61, year: 1954 }
    },
    
    # COORDINATOR class (0): Bridging, transformational works
    messiaen_turangalila: {
      name: "Messiaen: Turangalîla-Symphonie",
      form: :limit,
      trit: 0,
      domain: :modes,
      morphisms: [:non_retrogradable_rhythm, :color_chord, :birdsong],
      denotator: { movements: 10, ondes_martenot: true, love_theme: :cyclic }
    },
    bartok_mikrokosmos: {
      name: "Bartók: Mikrokosmos",
      form: :list,
      trit: 0,
      domain: :pedagogy,
      morphisms: [:folk_mode, :symmetry, :golden_section],
      denotator: { books: 6, pieces: 153, progressive: true }
    },
    stockhausen_klavierstucke: {
      name: "Stockhausen: Klavierstücke I-XI",
      form: :colimit,
      trit: 0,
      domain: :serialism,
      morphisms: [:pointillism, :moment_form, :variable_form],
      denotator: { pieces: 11, notation: :proportional, aleatoric: true }
    },
    
    # VALIDATOR class (-1): Constraining, structural works
    webern_variations: {
      name: "Webern: Variations for Piano Op. 27",
      form: :limit,
      trit: -1,
      domain: :serialism,
      morphisms: [:twelve_tone, :palindrome, :klangfarbenmelodie],
      denotator: { movements: 3, duration_min: 6, row_forms: 48 }
    },
    reich_piano_phase: {
      name: "Reich: Piano Phase",
      form: :list,
      trit: -1,
      domain: :minimalism,
      morphisms: [:phase_shift, :process, :gradual_change],
      denotator: { pianists: 2, pattern_notes: 12, phases: 32 }
    },
    feldman_triadic_memories: {
      name: "Feldman: Triadic Memories",
      form: :name,  # Reference type (NameForm)
      trit: -1,
      domain: :time_canvas,
      morphisms: [:near_repetition, :memory_trace, :carpet_weave],
      denotator: { duration_min: 90, triads: :chromatic, pedal: :sempre }
    }
  }
  
  # ═══════════════════════════════════════════════════════════════════════════
  # SKILL AGENTS (Bisimulation Game Roles)
  # ═══════════════════════════════════════════════════════════════════════════
  
  class SkillAgent
    attr_reader :name, :role, :trit, :color, :selections, :arguments
    
    def initialize(name, role, trit, seed)
      @name = name
      @role = role
      @trit = trit
      @color = case trit
               when +1 then "#D82626"  # Red
               when 0 then "#26D826"   # Green
               when -1 then "#2626D8"  # Blue
               end
      @gen = SplitMixTernary::Generator.new(seed)
      @selections = []
      @arguments = []
    end
    
    def propose(candidates)
      # Filter by compatible trit (same or complementary)
      compatible = candidates.select { |_, c| compatible_trit?(c[:trit]) }
      
      # Rank by domain affinity
      ranked = compatible.sort_by do |key, comp|
        -domain_affinity(comp) - (@gen.next_float * 0.3)  # Add deterministic noise
      end
      
      selection = ranked.first
      @selections << selection
      
      argument = generate_argument(selection)
      @arguments << argument
      
      { selection: selection, argument: argument }
    end
    
    def compatible_trit?(other_trit)
      # Compatible if: same polarity OR would help balance
      @trit == other_trit || (@trit + other_trit).abs <= 1
    end
    
    def domain_affinity(composition)
      case @role
      when :generator
        # Prefer generative domains
        case composition[:domain]
        when :counterpoint, :stochastic then 3
        when :rhythm then 2
        else 1
        end
      when :coordinator
        # Prefer bridging domains
        case composition[:domain]
        when :modes, :serialism, :pedagogy then 3
        when :minimalism then 2
        else 1
        end
      when :validator
        # Prefer constrained domains
        case composition[:domain]
        when :serialism, :minimalism, :time_canvas then 3
        when :counterpoint then 2
        else 1
        end
      end
    end
    
    def generate_argument(selection)
      key, comp = selection
      
      case @role
      when :generator
        "#{comp[:name]} exemplifies generative power through #{comp[:morphisms].first}. " \
        "Its #{comp[:form]} form enables #{comp[:morphisms].size} distinct transformations."
      when :coordinator
        "#{comp[:name]} bridges #{comp[:domain]} with universal structures. " \
        "World-hop via #{comp[:morphisms].sample}: conceptual distance minimized."
      when :validator
        "#{comp[:name]} satisfies bisimulation: observationally equivalent under #{comp[:morphisms].last}. " \
        "Structural invariant: #{comp[:denotator].keys.first} = #{comp[:denotator].values.first}."
      end
    end
    
    def vote_for(candidates, exclude: [])
      available = candidates.reject { |k, _| exclude.include?(k) }
      propose(available)
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════
  # ARGUMENTATION ENGINE
  # ═══════════════════════════════════════════════════════════════════════════
  
  class ArgumentationEngine
    attr_reader :agents, :rounds, :final_selections, :walk
    
    def initialize(seed = 0x42D)
      @seed = seed
      @agents = [
        SkillAgent.new("rubato-composer", :generator, +1, seed),
        SkillAgent.new("glass-bead-game", :coordinator, 0, (seed ^ 0xBEAD) & 0xFFFFFFFFFFFFFFFF),
        SkillAgent.new("bisimulation-game", :validator, -1, (seed ^ 0xB151) & 0xFFFFFFFFFFFFFFFF)
      ]
      @rounds = []
      @final_selections = []
      @walk = SelfAvoidingColoredWalk::Walk.new(seed)
    end
    
    def argue!
      candidates = COMPOSITIONS.dup
      selected_keys = []
      
      3.times do |round_num|
        # Walk step for this round
        @walk.step!
        
        round = { number: round_num + 1, proposals: [], walk_position: @walk.current.coords }
        
        # Each agent proposes
        @agents.each do |agent|
          proposal = agent.vote_for(candidates, exclude: selected_keys)
          round[:proposals] << {
            agent: agent.name,
            role: agent.role,
            trit: agent.trit,
            color: agent.color,
            selection: proposal[:selection][0],
            composition: proposal[:selection][1][:name],
            argument: proposal[:argument]
          }
        end
        
        # Consensus: select composition that best balances GF(3)
        current_trit_sum = @final_selections.sum { |s| s[:trit] }
        needed_trit = (0 - current_trit_sum) % 3
        needed_trit = needed_trit == 2 ? -1 : needed_trit  # Map 2 → -1
        
        # Find best candidate matching needed trit
        best_match = round[:proposals].find { |p| p[:composition] && candidates[p[:selection]]&.dig(:trit) == needed_trit }
        best_match ||= round[:proposals].first
        
        selected_key = best_match[:selection]
        selected_comp = candidates[selected_key]
        
        @final_selections << {
          round: round_num + 1,
          key: selected_key,
          name: selected_comp[:name],
          trit: selected_comp[:trit],
          form: selected_comp[:form],
          domain: selected_comp[:domain],
          selected_by: best_match[:agent],
          walk_trit: @walk.current.trit
        }
        
        selected_keys << selected_key
        round[:selected] = selected_key
        round[:gf3_running_sum] = @final_selections.sum { |s| s[:trit] }
        
        @rounds << round
      end
      
      verify_gf3!
      self
    end
    
    def verify_gf3!
      trit_sum = @final_selections.sum { |s| s[:trit] }
      @gf3_conserved = (trit_sum % 3) == 0
      @gf3_sum = trit_sum
    end
    
    def gf3_conserved?
      @gf3_conserved
    end
    
    def summary
      {
        compositions: @final_selections.map { |s| s[:name] },
        trits: @final_selections.map { |s| s[:trit] },
        gf3_sum: @gf3_sum,
        gf3_conserved: @gf3_conserved,
        domains: @final_selections.map { |s| s[:domain] },
        forms: @final_selections.map { |s| s[:form] }
      }
    end
    
    def to_s
      lines = []
      lines << "╔═══════════════════════════════════════════════════════════════════════════════╗"
      lines << "║  SKILLS ARGUE: Which 3 Compositions?                                         ║"
      lines << "║  GF(3) Triad: rubato(+1) ⊗ glass-bead(0) ⊗ bisimulation(-1) = 0              ║"
      lines << "╚═══════════════════════════════════════════════════════════════════════════════╝"
      lines << ""
      
      @rounds.each do |round|
        lines << "━━━ Round #{round[:number]} ━━━ Walk: (#{round[:walk_position].join(', ')})"
        round[:proposals].each do |p|
          trit_char = p[:trit] == 1 ? '+' : (p[:trit] == -1 ? '-' : '0')
          marker = p[:selection] == round[:selected] ? "★" : " "
          lines << "  #{marker} [#{trit_char}] #{p[:agent].ljust(18)} → #{p[:composition]}"
          lines << "      #{p[:argument][0..75]}..."
        end
        lines << "  GF(3) running sum: #{round[:gf3_running_sum]}"
        lines << ""
      end
      
      lines << "═══════════════════════════════════════════════════════════════════════════════"
      lines << "FINAL SELECTIONS:"
      @final_selections.each_with_index do |s, i|
        trit_char = s[:trit] == 1 ? '+' : (s[:trit] == -1 ? '-' : '0')
        lines << "  #{i+1}. [#{trit_char}] #{s[:name]}"
        lines << "       Form: #{s[:form]} | Domain: #{s[:domain]} | Selected by: #{s[:selected_by]}"
      end
      lines << ""
      lines << "GF(3) Conservation: #{@gf3_conserved ? '✓ CONSERVED' : '✗ VIOLATED'} (sum = #{@gf3_sum})"
      lines << "Walk is self-avoiding: #{@walk.spectral_summary[:is_self_avoiding] ? '✓' : '✗'}"
      lines << "═══════════════════════════════════════════════════════════════════════════════"
      
      lines.join("\n")
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════
  # MODULE METHODS
  # ═══════════════════════════════════════════════════════════════════════════
  
  def self.argue!(seed = 0x42D)
    engine = ArgumentationEngine.new(seed)
    engine.argue!
    engine
  end
  
  def self.demo(seed: 0x42D)
    engine = argue!(seed)
    puts engine.to_s
    engine
  end
  
  # ═══════════════════════════════════════════════════════════════════════════
  # WORLD BROADCAST INTEGRATION
  # ═══════════════════════════════════════════════════════════════════════════
  
  class CompositionBroadcast
    attr_reader :engine, :broadcast_log
    
    def initialize(seed = 0x42D)
      @engine = ArgumentationEngine.new(seed)
      @engine.argue!
      @broadcast_log = []
      @tripartite = SplitMixTernary::TripartiteStreams.new(seed)
    end
    
    def broadcast!(steps: 12)
      compositions = @engine.final_selections
      
      steps.times do |epoch|
        triplet = @tripartite.next_triplet
        comp_idx = epoch % 3
        comp = compositions[comp_idx]
        
        # Map composition morphisms to broadcast actions
        morphisms = COMPOSITIONS[comp[:key]][:morphisms]
        active_morphism = morphisms[epoch % morphisms.size]
        
        message = {
          epoch: epoch + 1,
          composition: comp[:name],
          trit: comp[:trit],
          domain: comp[:domain],
          form: comp[:form],
          morphism: active_morphism,
          triplet: triplet,
          gf3_conserved: triplet[:conserved]
        }
        
        @broadcast_log << message
      end
      
      self
    end
    
    def to_s
      lines = []
      lines << "╔═══════════════════════════════════════════════════════════════════╗"
      lines << "║  COMPOSITION BROADCAST: #{@engine.final_selections.map { |s| s[:name].split(':').first }.join(' ⊗ ')}"
      lines << "╚═══════════════════════════════════════════════════════════════════╝"
      lines << ""
      
      @broadcast_log.each do |msg|
        trit_char = msg[:trit] == 1 ? '+' : (msg[:trit] == -1 ? '-' : '0')
        trip = "[#{msg[:triplet][:minus]},#{msg[:triplet][:ergodic]},#{msg[:triplet][:plus]}]"
        lines << "Epoch #{msg[:epoch].to_s.rjust(2)}: [#{trit_char}] #{msg[:composition].ljust(35)} → #{msg[:morphism]} #{trip}"
      end
      
      lines << ""
      lines << "All GF(3) conserved: #{@broadcast_log.all? { |m| m[:gf3_conserved] } ? '✓' : '✗'}"
      lines.join("\n")
    end
  end
  
  def self.broadcast!(seed: 0x42D, steps: 12)
    cb = CompositionBroadcast.new(seed)
    cb.broadcast!(steps: steps)
    puts cb.to_s
    cb
  end
  
  # ═══════════════════════════════════════════════════════════════════════════
  # DUCKDB PERSISTENCE
  # ═══════════════════════════════════════════════════════════════════════════
  
  def self.persist_to_duckdb!(db_path: "compositions.duckdb", seed: 0x42D)
    require 'open3'
    
    engine = argue!(seed)
    
    # Generate SQL inserts
    sql_lines = []
    sql_lines << ".read db/compositions_schema.sql"
    
    # Insert compositions
    engine.final_selections.each do |sel|
      comp = COMPOSITIONS[sel[:key]]
      composer = sel[:name].split(':').first.strip
      sql_lines << "INSERT OR REPLACE INTO compositions VALUES ('#{sel[:key]}', '#{sel[:name].gsub("'", "''")}', '#{composer}', '#{comp[:form]}', #{comp[:trit]}, '#{comp[:domain]}', NULL, NULL, current_timestamp);"
      
      # Insert morphisms
      comp[:morphisms].each_with_index do |morph, i|
        sql_lines << "INSERT OR REPLACE INTO composition_morphisms VALUES ('#{sel[:key]}_#{morph}', '#{sel[:key]}', '#{morph}', #{i}, current_timestamp);"
      end
      
      # Insert denotators
      comp[:denotator].each do |k, v|
        val_str = v.is_a?(Array) ? v.join(',') : v.to_s
        sql_lines << "INSERT OR REPLACE INTO composition_denotators VALUES ('#{sel[:key]}', '#{k}', '#{val_str.gsub("'", "''")}');"
      end
    end
    
    # Insert argumentation rounds
    engine.rounds.each_with_index do |round, i|
      sel = engine.final_selections[i]
      walk_pos = round[:walk_position].to_s
      sql_lines << "INSERT INTO argumentation_rounds VALUES ('#{seed.to_s(16)}_r#{i+1}', '0x#{seed.to_s(16)}', #{i+1}, '#{sel[:key]}', '#{sel[:selected_by]}', '#{walk_pos}', #{round[:gf3_running_sum]}, current_timestamp);"
    end
    
    sql = sql_lines.join("\n")
    
    # Execute via duckdb CLI
    stdout, stderr, status = Open3.capture3("duckdb #{db_path}", stdin_data: sql)
    
    if status.success?
      puts "✓ Persisted #{engine.final_selections.size} compositions to #{db_path}"
      { success: true, db_path: db_path, compositions: engine.final_selections.map { |s| s[:name] } }
    else
      puts "✗ DuckDB error: #{stderr}"
      { success: false, error: stderr }
    end
  end
end

if __FILE__ == $0
  SkillsArgueCompositions.demo
end
