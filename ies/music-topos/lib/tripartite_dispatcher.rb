# lib/tripartite_dispatcher.rb
#
# Tripartite Subagent Dispatcher
# Assigns tasks to MINUS/ERGODIC/PLUS subagents based on GF(3) conservation
#
# Each triad: (-1) ⊗ (0) ⊗ (+1) = 0
#

require_relative 'splitmix_ternary'

module TripartiteDispatcher
  # ═══════════════════════════════════════════════════════════════════════════════
  # SKILL REGISTRY WITH TRITS
  # ═══════════════════════════════════════════════════════════════════════════════
  
  SKILLS = {
    # MINUS (-1): Validators
    'sheaf-cohomology'    => { trit: -1, bundle: :cohomological, action: :verify },
    'temporal-coalgebra'  => { trit: -1, bundle: :game, action: :observe },
    'persistent-homology' => { trit: -1, bundle: :topos, action: :filter },
    'three-match'         => { trit: -1, bundle: :core, action: :reduce },
    'clj-kondo-3color'    => { trit: -1, bundle: :database, action: :lint },
    'proofgeneral-narya'  => { trit: -1, bundle: :strategic, action: :prove },
    'slime-lisp'          => { trit: -1, bundle: :repl, action: :evaluate },
    'hatchery-papers'     => { trit: -1, bundle: :research, action: :cite },
    
    # ERGODIC (0): Coordinators
    'kan-extensions'      => { trit: 0, bundle: :cohomological, action: :migrate },
    'dialectica'          => { trit: 0, bundle: :game, action: :transport },
    'open-games'          => { trit: 0, bundle: :topos, action: :compose },
    'unworld'             => { trit: 0, bundle: :core, action: :derive },
    'acsets'              => { trit: 0, bundle: :database, action: :query },
    'glass-bead-game'     => { trit: 0, bundle: :strategic, action: :hop },
    'borkdude'            => { trit: 0, bundle: :repl, action: :script },
    'mathpix-ocr'         => { trit: 0, bundle: :research, action: :extract },
    
    # PLUS (+1): Generators
    'free-monad-gen'      => { trit: 1, bundle: :cohomological, action: :generate },
    'operad-compose'      => { trit: 1, bundle: :game, action: :multiply },
    'topos-generate'      => { trit: 1, bundle: :topos, action: :force },
    'gay-mcp'             => { trit: 1, bundle: :core, action: :color },
    'rama-gay-clojure'    => { trit: 1, bundle: :database, action: :emit },
    'rubato-composer'     => { trit: 1, bundle: :strategic, action: :compose },
    'cider-clojure'       => { trit: 1, bundle: :repl, action: :jack_in },
    'bmorphism-stars'     => { trit: 1, bundle: :research, action: :curate }
  }.freeze
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # CANONICAL TRIADS
  # ═══════════════════════════════════════════════════════════════════════════════
  
  TRIADS = {
    cohomological: %w[sheaf-cohomology kan-extensions free-monad-gen],
    game:          %w[temporal-coalgebra dialectica operad-compose],
    topos:         %w[persistent-homology open-games topos-generate],
    core:          %w[three-match unworld gay-mcp],
    database:      %w[clj-kondo-3color acsets rama-gay-clojure],
    strategic:     %w[proofgeneral-narya glass-bead-game rubato-composer],
    repl:          %w[slime-lisp borkdude cider-clojure],
    research:      %w[hatchery-papers mathpix-ocr bmorphism-stars]
  }.freeze
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # SUBAGENT ROLES
  # ═══════════════════════════════════════════════════════════════════════════════
  
  ROLES = {
    -1 => { name: :validator,   color: '#2626D8', verbs: %i[verify constrain reduce filter] },
     0 => { name: :coordinator, color: '#26D826', verbs: %i[transport derive navigate bridge] },
     1 => { name: :generator,   color: '#D82626', verbs: %i[create compose generate expand] }
  }.freeze
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # DISPATCHER
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class Dispatcher
    attr_reader :seed, :dispatched
    
    def initialize(seed = 0xf061ebbc2ca74d78)
      @seed = seed
      @rng = SplitMixTernary.new(seed)
      @dispatched = []
    end
    
    # Dispatch a task to appropriate subagent
    def dispatch(task, bundle: nil, prefer_trit: nil)
      # Determine bundle from task if not specified
      bundle ||= infer_bundle(task)
      
      # Get triad for bundle
      triad = TRIADS[bundle] || TRIADS[:core]
      
      # Assign subagents
      assignments = triad.map do |skill|
        info = SKILLS[skill]
        role = ROLES[info[:trit]]
        {
          skill: skill,
          trit: info[:trit],
          role: role[:name],
          color: role[:color],
          action: info[:action]
        }
      end
      
      # Record dispatch
      dispatch_record = {
        task: task,
        bundle: bundle,
        triad: triad,
        assignments: assignments,
        gf3_sum: assignments.sum { |a| a[:trit] },
        timestamp: Time.now,
        seed: @rng.next_seed
      }
      
      @dispatched << dispatch_record
      dispatch_record
    end
    
    # Execute a full triad pipeline
    def execute_triad(bundle, input)
      triad = TRIADS[bundle]
      raise "Unknown bundle: #{bundle}" unless triad
      
      results = []
      current = input
      
      # Execute in order: MINUS → ERGODIC → PLUS (sorted by trit)
      sorted = triad.sort_by { |s| SKILLS[s][:trit] }
      
      sorted.each do |skill|
        info = SKILLS[skill]
        role = ROLES[info[:trit]]
        
        result = {
          skill: skill,
          trit: info[:trit],
          role: role[:name],
          input: current,
          output: yield(skill, current, info),
          color: role[:color]
        }
        
        results << result
        current = result[:output]
      end
      
      {
        bundle: bundle,
        pipeline: results,
        final_output: current,
        gf3_conserved: results.sum { |r| r[:trit] } % 3 == 0
      }
    end
    
    # Find optimal triad for a domain
    def triad_for(domain)
      # Search by action verb
      TRIADS.find do |bundle, skills|
        skills.any? do |skill|
          info = SKILLS[skill]
          info[:action].to_s.include?(domain.to_s) ||
            skill.include?(domain.to_s)
        end
      end&.first || :core
    end
    
    # Get skill by role from bundle
    def skill_by_role(bundle, role)
      triad = TRIADS[bundle]
      return nil unless triad
      
      target_trit = case role
                    when :validator, :minus   then -1
                    when :coordinator, :ergodic then 0
                    when :generator, :plus    then 1
                    else return nil
                    end
      
      triad.find { |s| SKILLS[s][:trit] == target_trit }
    end
    
    # Cross-bundle composition: take one skill from each polarity
    def cross_compose(minus_bundle, ergodic_bundle, plus_bundle)
      minus_skill = skill_by_role(minus_bundle, :minus)
      ergodic_skill = skill_by_role(ergodic_bundle, :ergodic)
      plus_skill = skill_by_role(plus_bundle, :plus)
      
      {
        triad: [minus_skill, ergodic_skill, plus_skill],
        bundles: [minus_bundle, ergodic_bundle, plus_bundle],
        gf3_sum: -1 + 0 + 1,
        conserved: true
      }
    end
    
    # Generate report
    def report
      {
        total_dispatches: @dispatched.length,
        by_bundle: @dispatched.group_by { |d| d[:bundle] }
                              .transform_values(&:count),
        all_conserved: @dispatched.all? { |d| d[:gf3_sum] % 3 == 0 },
        seed: @seed
      }
    end
    
    private
    
    def infer_bundle(task)
      task_str = task.to_s.downcase
      
      case task_str
      when /cohomolog|sheaf|kan|free/     then :cohomological
      when /game|dialectica|operad/       then :game
      when /topos|homolog|forc/           then :topos
      when /match|unworld|color|gay/      then :core
      when /kondo|acset|rama|database/    then :database
      when /proof|glass|rubato|strategic/ then :strategic
      when /lisp|slime|bork|cider|repl/   then :repl
      when /paper|mathpix|star|research/  then :research
      else :core
      end
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # CONVENIENCE METHODS
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.dispatch(task, **opts)
    Dispatcher.new.dispatch(task, **opts)
  end
  
  def self.triads
    TRIADS
  end
  
  def self.skills_by_trit(trit)
    SKILLS.select { |_, v| v[:trit] == trit }.keys
  end
  
  def self.verify_all_triads
    TRIADS.map do |bundle, skills|
      sum = skills.sum { |s| SKILLS[s][:trit] }
      { bundle: bundle, skills: skills, sum: sum, conserved: sum % 3 == 0 }
    end
  end
end

# ═══════════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════════

if __FILE__ == $0
  require 'json'
  
  dispatcher = TripartiteDispatcher::Dispatcher.new
  
  case ARGV[0]
  when 'dispatch'
    task = ARGV[1] || 'default'
    bundle = ARGV[2]&.to_sym
    result = dispatcher.dispatch(task, bundle: bundle)
    puts JSON.pretty_generate(result)
    
  when 'execute'
    bundle = (ARGV[1] || 'core').to_sym
    result = dispatcher.execute_triad(bundle, ARGV[2] || 'input') do |skill, input, info|
      "#{skill}(#{input})"
    end
    puts JSON.pretty_generate(result)
    
  when 'verify'
    results = TripartiteDispatcher.verify_all_triads
    results.each do |r|
      status = r[:conserved] ? '✓' : '✗'
      puts "#{r[:bundle]}: #{r[:skills].join(' ⊗ ')} = #{r[:sum]} #{status}"
    end
    
  when 'cross'
    m, e, p = ARGV[1..3].map(&:to_sym)
    result = dispatcher.cross_compose(m || :cohomological, e || :game, p || :topos)
    puts JSON.pretty_generate(result)
    
  else
    puts "Usage:"
    puts "  ruby tripartite_dispatcher.rb dispatch <task> [bundle]"
    puts "  ruby tripartite_dispatcher.rb execute <bundle> [input]"
    puts "  ruby tripartite_dispatcher.rb verify"
    puts "  ruby tripartite_dispatcher.rb cross <minus_bundle> <ergodic_bundle> <plus_bundle>"
  end
end
