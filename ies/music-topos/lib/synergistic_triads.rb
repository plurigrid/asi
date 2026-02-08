# lib/synergistic_triads.rb
#
# SYNERGISTIC 3-TUPLES: Skill Loading with GF(3) Conservation
#
# Each skill has a trit: -1 (MINUS), 0 (ERGODIC), +1 (PLUS)
# Three skills form a synergistic triad when trits sum to 0 mod 3
# Subagent determination follows from triadic structure
#
# Example: three-match (-1) + gay-mcp (+1) + unworld (0) = 0 ✓

require_relative 'splitmix_ternary'

module SynergisticTriads
  # ═══════════════════════════════════════════════════════════════════════════════
  # SKILL REGISTRY: All 29 skills with trit assignments
  # ═══════════════════════════════════════════════════════════════════════════════
  
  SKILLS = {
    # MINUS (-1): Conservative, contravariant, geodesic
    'three-match'       => { trit: -1, polarity: :minus, domain: :reduction },
    'slime-lisp'        => { trit: -1, polarity: :minus, domain: :repl },
    'clj-kondo-3color'  => { trit: -1, polarity: :minus, domain: :linting },
    'hatchery-papers'   => { trit: -1, polarity: :minus, domain: :research },
    'proofgeneral-narya'=> { trit: -1, polarity: :minus, domain: :verification },
    
    # ERGODIC (0): Neutral, transport, derivational
    'unworld'             => { trit: 0, polarity: :ergodic, domain: :derivation },
    'unworlding-involution' => { trit: 0, polarity: :ergodic, domain: :involution },
    'borkdude'            => { trit: 0, polarity: :ergodic, domain: :runtime },
    'squint-runtime'      => { trit: 0, polarity: :ergodic, domain: :runtime },
    'cider-embedding'     => { trit: 0, polarity: :ergodic, domain: :navigation },
    'epistemic-arbitrage' => { trit: 0, polarity: :ergodic, domain: :propagation },
    'world-hopping'       => { trit: 0, polarity: :ergodic, domain: :navigation },
    'acsets'              => { trit: 0, polarity: :ergodic, domain: :database },
    'bisimulation-game'   => { trit: 0, polarity: :ergodic, domain: :game },
    'glass-bead-game'     => { trit: 0, polarity: :ergodic, domain: :game },
    'discohy-streams'     => { trit: 0, polarity: :ergodic, domain: :streaming },
    'triad-interleave'    => { trit: 0, polarity: :ergodic, domain: :interleave },
    'codex-self-rewriting'=> { trit: 0, polarity: :ergodic, domain: :metaprogramming },
    'mathpix-ocr'         => { trit: 0, polarity: :ergodic, domain: :ocr },
    'self-validation-loop'=> { trit: 0, polarity: :ergodic, domain: :validation },
    'spi-parallel-verify' => { trit: 0, polarity: :ergodic, domain: :verification },
    
    # PLUS (+1): Additive, covariant, generative
    'gay-mcp'           => { trit: 1, polarity: :plus, domain: :color },
    'cider-clojure'     => { trit: 1, polarity: :plus, domain: :repl },
    'geiser-chicken'    => { trit: 1, polarity: :plus, domain: :repl },
    'rama-gay-clojure'  => { trit: 1, polarity: :plus, domain: :framework },
    'rubato-composer'   => { trit: 1, polarity: :plus, domain: :composition },
    'frontend-design'   => { trit: 1, polarity: :plus, domain: :design },
    'bmorphism-stars'   => { trit: 1, polarity: :plus, domain: :curation },
    'xenodium-elisp'    => { trit: 1, polarity: :plus, domain: :elisp }
  }.freeze
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # TRIAD FORMATION: Find valid 3-tuples where trits sum to 0 mod 3
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class Triad
    attr_reader :skills, :trits, :sum, :valid
    
    def initialize(skill1, skill2, skill3)
      @skills = [skill1, skill2, skill3].sort
      @trits = @skills.map { |s| SKILLS.dig(s, :trit) || 0 }
      @sum = @trits.sum
      @valid = (@sum % 3) == 0
    end
    
    def gf3_conserved?
      @valid
    end
    
    # Subagent assignment based on trit polarity
    def subagent_assignment
      @skills.zip(@trits).map do |skill, trit|
        case trit
        when -1 then { skill: skill, subagent: :validator, role: :conservative }
        when 0  then { skill: skill, subagent: :coordinator, role: :neutral }
        when 1  then { skill: skill, subagent: :generator, role: :generative }
        end
      end
    end
    
    def to_s
      signs = @trits.map { |t| t == -1 ? '-' : (t == 1 ? '+' : '0') }
      "Triad(#{@skills.join(' ⊗ ')}) = #{signs.join(' + ')} = #{@sum} #{@valid ? '✓' : '✗'}"
    end
    
    def to_h
      {
        skills: @skills,
        trits: @trits,
        sum: @sum,
        gf3_conserved: @valid,
        subagents: subagent_assignment
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # CANONICAL TRIADS: Pre-computed synergistic combinations
  # ═══════════════════════════════════════════════════════════════════════════════
  
  CANONICAL_TRIADS = [
    # Core system triad: reduction (-1) + derivation (0) + generation (+1) = 0 ✓
    %w[three-match unworld gay-mcp],
    
    # REPL triad: slime (-1) + borkdude (0) + cider (+1) = 0 ✓
    %w[slime-lisp borkdude cider-clojure],
    
    # Game theory triad: three-match (-1) + bisimulation (0) + rubato (+1) = 0 ✓
    %w[three-match bisimulation-game rubato-composer],
    
    # Navigation triad: slime (-1) + world-hopping (0) + geiser (+1) = 0 ✓
    %w[slime-lisp world-hopping geiser-chicken],
    
    # Database triad: clj-kondo (-1) + acsets (0) + rama-gay (+1) = 0 ✓
    %w[clj-kondo-3color acsets rama-gay-clojure],
    
    # Verification triad: clj-kondo (-1) + spi-parallel (0) + frontend (+1) = 0 ✓
    %w[clj-kondo-3color spi-parallel-verify frontend-design],
    
    # Research triad: hatchery (-1) + mathpix (0) + bmorphism (+1) = 0 ✓
    %w[hatchery-papers mathpix-ocr bmorphism-stars],
    
    # Metaprogramming triad: proofgeneral (-1) + codex (0) + xenodium (+1) = 0 ✓
    %w[proofgeneral-narya codex-self-rewriting xenodium-elisp],
    
    # Involution triad: all ergodic (0+0+0) = 0 ✓
    %w[unworlding-involution self-validation-loop cider-embedding],
    
    # Runtime triad: proofgeneral (-1) + squint (0) + gay (+1) = 0 ✓
    %w[proofgeneral-narya squint-runtime gay-mcp],
    
    # Glass bead game triad: three-match (-1) + glass-bead (0) + cider (+1) = 0 ✓
    %w[three-match glass-bead-game cider-clojure],
    
    # Streaming triad: hatchery (-1) + discohy (0) + frontend (+1) = 0 ✓
    %w[hatchery-papers discohy-streams frontend-design],
    
    # Arbitrage triad: slime (-1) + epistemic (0) + bmorphism (+1) = 0 ✓
    %w[slime-lisp epistemic-arbitrage bmorphism-stars]
  ].freeze
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # TRIAD FINDER: Discover all valid triads from skill set
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.find_all_valid_triads
    skills = SKILLS.keys
    valid = []
    
    skills.combination(3).each do |combo|
      triad = Triad.new(*combo)
      valid << triad if triad.gf3_conserved?
    end
    
    valid
  end
  
  # Find triads containing a specific skill
  def self.triads_for_skill(skill_name)
    find_all_valid_triads.select { |t| t.skills.include?(skill_name) }
  end
  
  # Find replacement triads (skills that can substitute)
  def self.replacement_triads(skill_name, target_trit)
    SKILLS.select { |_, v| v[:trit] == target_trit }
          .keys
          .reject { |s| s == skill_name }
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # SUBAGENT DETERMINATION: Assign skills to subagents based on triads
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class SubagentDeterminer
    SUBAGENT_ROLES = {
      validator:   { trit: -1, color: '#2626D8', action: :verify },
      coordinator: { trit: 0,  color: '#26D826', action: :coordinate },
      generator:   { trit: 1,  color: '#D82626', action: :generate }
    }.freeze
    
    def initialize(seed: 0x42D)
      @seed = seed
      @rng = SplitMixTernary::Generator.new(seed)
    end
    
    # Given a task, determine which triad of skills to use
    def determine_triad(task_domain)
      candidates = CANONICAL_TRIADS.select do |skills|
        skills.any? { |s| SKILLS.dig(s, :domain) == task_domain }
      end
      
      return CANONICAL_TRIADS.first if candidates.empty?
      
      # Use deterministic selection based on seed
      idx = @rng.next_u64 % candidates.size
      candidates[idx]
    end
    
    # Assign skills to subagents for a given triad
    def assign_subagents(triad_skills)
      triad = Triad.new(*triad_skills)
      
      triad.subagent_assignment.map do |assignment|
        role_info = SUBAGENT_ROLES[assignment[:subagent]]
        assignment.merge(
          color: role_info[:color],
          action: role_info[:action]
        )
      end
    end
    
    # Execute a task with triadic subagent structure
    def execute_with_triad(task_domain)
      triad_skills = determine_triad(task_domain)
      assignments = assign_subagents(triad_skills)
      
      {
        task_domain: task_domain,
        triad: triad_skills,
        subagents: assignments,
        gf3_sum: assignments.sum { |a| SKILLS.dig(a[:skill], :trit) || 0 }
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # DEMONSTRATION
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.demo
    puts "╔═══════════════════════════════════════════════════════════════════════════════╗"
    puts "║  SYNERGISTIC 3-TUPLES: Skill Loading with GF(3) Conservation                  ║"
    puts "╚═══════════════════════════════════════════════════════════════════════════════╝"
    puts
    
    puts "─── Skill Trit Assignments ───"
    [:minus, :ergodic, :plus].each do |polarity|
      trit = { minus: -1, ergodic: 0, plus: 1 }[polarity]
      skills = SKILLS.select { |_, v| v[:polarity] == polarity }.keys
      puts "  #{polarity.upcase} (#{trit >= 0 ? '+' : ''}#{trit}): #{skills.join(', ')}"
    end
    puts
    
    puts "─── Canonical Triads ───"
    CANONICAL_TRIADS.each do |skills|
      triad = Triad.new(*skills)
      puts "  #{triad}"
    end
    puts
    
    puts "─── Subagent Determination ───"
    determiner = SubagentDeterminer.new
    
    [:reduction, :derivation, :color, :game, :repl].each do |domain|
      result = determiner.execute_with_triad(domain)
      puts "  Task: #{domain}"
      result[:subagents].each do |a|
        puts "    #{a[:subagent]}: #{a[:skill]} (#{a[:action]})"
      end
      puts "    GF(3) = #{result[:gf3_sum]} #{result[:gf3_sum] % 3 == 0 ? '✓' : '✗'}"
      puts
    end
    
    puts "─── All Valid Triads Count ───"
    all_triads = find_all_valid_triads
    puts "  Total valid triads: #{all_triads.size}"
    puts "  Triads containing 'unworld': #{triads_for_skill('unworld').size}"
    puts "  Triads containing 'three-match': #{triads_for_skill('three-match').size}"
    puts
    
    puts "═══════════════════════════════════════════════════════════════════════════════"
    puts "GF(3) Conservation: Sum of trits ≡ 0 (mod 3) for all triads"
    puts "Subagent Roles: validator (-1), coordinator (0), generator (+1)"
    puts "═══════════════════════════════════════════════════════════════════════════════"
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # COLORED OUTPUT: Generate colored triads using deterministic colors
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.colored_triad(skills, seed: 0x42D)
    triad = Triad.new(*skills)
    rng = SplitMixTernary::Generator.new(seed)
    
    colors = skills.map.with_index do |skill, i|
      info = SKILLS[skill]
      base_color = case info[:trit]
                   when -1 then '#2626D8'  # Blue
                   when 0  then '#26D826'  # Green
                   when 1  then '#D82626'  # Red
                   end
      { skill: skill, trit: info[:trit], color: base_color, polarity: info[:polarity] }
    end
    
    {
      skills: skills,
      colors: colors,
      gf3_sum: triad.trits.sum,
      conserved: triad.gf3_conserved?,
      subagents: triad.subagent_assignment
    }
  end
  
  # Find replacement skills for a given skill (same trit)
  def self.replacements_for(skill_name)
    info = SKILLS[skill_name]
    return [] unless info
    
    SKILLS.select { |name, data| data[:trit] == info[:trit] && name != skill_name }
          .map { |name, data| { skill: name, domain: data[:domain] } }
  end
  
  # Immediate skill loading for subagent determination
  def self.load_triad_for_task(task_domain, seed: 0x42D)
    determiner = SubagentDeterminer.new(seed: seed)
    result = determiner.execute_with_triad(task_domain)
    
    puts "Loading triad for task: #{task_domain}"
    result[:subagents].each do |a|
      puts "  #{a[:subagent].to_s.upcase}: #{a[:skill]} (#{a[:action]}) #{a[:color]}"
    end
    puts "  GF(3) = #{result[:gf3_sum]} ✓" if result[:gf3_sum] % 3 == 0
    
    result
  end
end

if __FILE__ == $0
  SynergisticTriads.demo
end
