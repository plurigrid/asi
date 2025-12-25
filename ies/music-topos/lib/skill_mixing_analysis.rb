# Skill Mixing Time Analysis with Logical Clocks
#
# Measures how long information takes to propagate through the skill network
# using Lamport clocks and causality tracking.
#
# Key concepts:
# - Logical clock: counts causal events in the system
# - Mixing time: rounds until system reaches quasi-stationarity
# - Skill trit: GF(3) polarity (-1, 0, +1) affects coupling strength

require 'yaml'
require 'json'
require 'time'
require 'set'
require 'fileutils'

module SkillMixingAnalysis
  # ============================================================================
  # LOGICAL CLOCK: Lamport timestamp for causal ordering
  # ============================================================================

  class LogicalClock
    attr_reader :time
    attr_reader :node_id
    attr_reader :history

    def initialize(node_id)
      @node_id = node_id
      @time = 0
      @history = []
    end

    # Increment clock on local event
    def tick
      @time += 1
      @history << {event: :local, time: @time, node: @node_id}
      @time
    end

    # Update clock when receiving message from another node
    def receive(remote_time)
      @time = [@time, remote_time].max + 1
      @history << {event: :receive, time: @time, remote: remote_time, node: @node_id}
      @time
    end

    # Current logical time
    def now
      @time
    end

    def to_s
      "#{@node_id}:#{@time}"
    end
  end

  # ============================================================================
  # SKILL: Represents a single skill with metadata and clock
  # ============================================================================

  class Skill
    attr_reader :name
    attr_reader :trit
    attr_reader :version
    attr_reader :dependencies
    attr_reader :bundle
    attr_reader :clock
    attr_reader :date
    attr_accessor :mixed_at

    def initialize(name, trit: 0, version: "1.0.0", bundle: "core", date: Time.now)
      @name = name
      @trit = trit  # -1 (MINUS), 0 (ERGODIC), +1 (PLUS)
      @version = version
      @bundle = bundle
      @dependencies = Set.new
      @clock = LogicalClock.new(name)
      @date = date
      @mixed_at = nil
    end

    def add_dependency(skill_name)
      @dependencies << skill_name
    end

    def depends_on?(skill_name)
      @dependencies.include?(skill_name)
    end

    def tick
      @clock.tick
    end

    def receive(remote_time)
      @clock.receive(remote_time)
    end

    # GF(3) role string
    def role
      case @trit
      when -1
        "MINUS (validator)"
      when 0
        "ERGODIC (coordinator)"
      when 1
        "PLUS (generator)"
      else
        "UNKNOWN"
      end
    end

    def to_h
      {
        name: @name,
        trit: @trit,
        role: role,
        version: @version,
        bundle: @bundle,
        clock: @clock.now,
        dependencies: @dependencies.to_a,
        mixed_at: @mixed_at
      }
    end
  end

  # ============================================================================
  # SKILL NETWORK: DAG of skills with dependencies
  # ============================================================================

  class SkillNetwork
    attr_reader :skills
    attr_reader :mixing_times
    attr_reader :propagation_timeline

    def initialize
      @skills = {}
      @mixing_times = {}
      @propagation_timeline = []
    end

    # Add a skill to the network
    def add_skill(name, trit: 0, version: "1.0.0", bundle: "core", date: Time.now)
      skill = Skill.new(name, trit: trit, version: version, bundle: bundle, date: date)
      @skills[name] = skill
      skill
    end

    # Add dependency between skills
    def add_dependency(from_skill, to_skill)
      if @skills[from_skill] && @skills[to_skill]
        @skills[from_skill].add_dependency(to_skill)
      else
        raise "Skill not found: #{from_skill} or #{to_skill}"
      end
    end

    # Get topological sort (dependencies first)
    def topological_sort
      visited = Set.new
      sorted = []

      def visit(skill_name, visited, sorted, skills)
        return if visited.include?(skill_name)
        visited << skill_name

        # Visit dependencies first
        skills[skill_name].dependencies.each do |dep|
          visit(dep, visited, sorted, skills)
        end

        sorted << skill_name
      end

      @skills.keys.each do |skill_name|
        visit(skill_name, visited, sorted, @skills)
      end

      sorted
    end

    # Simulate one round: each skill receives from dependencies
    def simulate_round(round_num)
      round_data = {round: round_num, events: []}

      topological_sort.each do |skill_name|
        skill = @skills[skill_name]

        # Receive from all dependencies
        skill.dependencies.each do |dep_name|
          dep_skill = @skills[dep_name]
          remote_clock = dep_skill.clock.now
          skill.receive(remote_clock)

          round_data[:events] << {
            skill: skill_name,
            received_from: dep_name,
            remote_clock: remote_clock,
            new_clock: skill.clock.now
          }
        end

        # Local tick
        skill.tick
        round_data[:events] << {skill: skill_name, event: :tick, clock: skill.clock.now}
      end

      @propagation_timeline << round_data
      round_data
    end

    # Measure mixing time: rounds until stabilization
    # Convergence criterion: clock differences stabilize (entropy stops changing)
    def measure_mixing_time(max_rounds: 100, tolerance: 0.01)
      entropy_history = []
      mixing_round = nil

      max_rounds.times do |round_num|
        simulate_round(round_num)

        # Compute clock distribution entropy
        clocks = @skills.values.map(&:clock).map(&:now)
        entropy = compute_entropy(clocks)
        entropy_history << entropy

        # Check convergence: if entropy change is small for N consecutive rounds
        if entropy_history.size >= 10
          recent_changes = entropy_history[-10..-1].each_cons(2).map { |a, b| (b - a).abs }
          avg_change = recent_changes.sum / recent_changes.size

          if avg_change < tolerance && mixing_round.nil?
            mixing_round = round_num
          end
        end
      end

      @mixing_times[:entropy_history] = entropy_history
      @mixing_times[:mixing_round] = mixing_round || max_rounds
      @mixing_times[:final_entropy] = entropy_history.last
      @mixing_times[:converged] = mixing_round.nil? ? false : true

      mixing_round || max_rounds
    end

    # Shannon entropy of clock distribution
    def compute_entropy(clocks)
      return 0.0 if clocks.empty?
      return 0.0 if clocks.size == 1

      # Normalize clocks to probabilities
      max_clock = clocks.max.to_f
      return 0.0 if max_clock == 0

      normalized = clocks.map { |c| c.to_f / max_clock }

      # Compute entropy: -∑ p_i * log(p_i)
      entropy = 0.0
      normalized.each do |p|
        entropy -= p * Math.log(p) if p > 0 && p < 1
      end

      # Normalize to [0, 1]
      max_entropy = Math.log(clocks.size)
      max_entropy > 0 ? entropy / max_entropy : 0.0
    end

    # Analyze GF(3) conservation across network
    def analyze_gf3_conservation
      trits = @skills.values.map(&:trit)
      sum_mod_3 = trits.sum % 3
      counts = {minus_1: 0, zero: 0, plus_1: 0}

      trits.each do |t|
        case t
        when -1
          counts[:minus_1] += 1
        when 0
          counts[:zero] += 1
        when 1
          counts[:plus_1] += 1
        end
      end

      {
        sum_mod_3: sum_mod_3,
        counts: counts,
        conserved: sum_mod_3 == 0,
        ratio: "#{counts[:minus_1]}:#{counts[:zero]}:#{counts[:plus_1]}"
      }
    end

    # Find shortest path (mixing distance) from skill A to skill B
    def shortest_path(from_skill, to_skill)
      queue = [[from_skill, [from_skill]]]
      visited = Set.new([from_skill])

      while queue.any?
        current, path = queue.shift

        return path if current == to_skill

        @skills[current].dependencies.each do |dep|
          unless visited.include?(dep)
            visited << dep
            queue << [dep, path + [dep]]
          end
        end
      end

      nil  # No path found
    end

    # Average mixing distance across all pairs
    def average_mixing_distance
      distances = []

      @skills.each_key do |from_skill|
        @skills.each_key do |to_skill|
          next if from_skill == to_skill
          path = shortest_path(from_skill, to_skill)
          distances << (path ? path.length - 1 : Float::INFINITY)
        end
      end

      valid_distances = distances.reject { |d| d == Float::INFINITY }
      return 0.0 if valid_distances.empty?

      valid_distances.sum.to_f / valid_distances.size
    end

    # Diameter: longest shortest path
    def diameter
      max_distance = 0

      @skills.each_key do |from_skill|
        @skills.each_key do |to_skill|
          next if from_skill == to_skill
          path = shortest_path(from_skill, to_skill)
          distance = path ? path.length - 1 : Float::INFINITY
          max_distance = distance if distance < Float::INFINITY && distance > max_distance
        end
      end

      max_distance
    end

    def to_json
      # Convert mixing times, filtering out NaN/Infinity
      safe_mixing_times = {}
      @mixing_times.each do |key, value|
        if value.is_a?(Array)
          safe_mixing_times[key] = value.map { |v| v.is_a?(Float) && !v.finite? ? 0.0 : v }
        elsif value.is_a?(Float) && !value.finite?
          safe_mixing_times[key] = 0.0
        else
          safe_mixing_times[key] = value
        end
      end

      avg_dist = average_mixing_distance
      safe_avg_dist = avg_dist.finite? ? avg_dist : 0.0

      {
        skills: @skills.map { |name, skill| [name, skill.to_h] }.to_h,
        mixing_times: safe_mixing_times,
        statistics: {
          count: @skills.size,
          gf3_conservation: analyze_gf3_conservation,
          average_mixing_distance: safe_avg_dist,
          network_diameter: diameter
        }
      }
    end
  end

  # ============================================================================
  # SKILL LOADER: Load skills from filesystem
  # ============================================================================

  class SkillLoader
    def self.load_from_directory(dir_path)
      network = SkillNetwork.new

      # Load from all standard skill directories
      skill_dirs = ['.agents/skills', '.codex/skills', '.ruler/skills', '.cursor/skills']
      all_skill_files = []

      skill_dirs.each do |skill_dir|
        full_path = File.join(dir_path, skill_dir)
        Dir.glob("#{full_path}/**/SKILL.md").each do |skill_file|
          all_skill_files << skill_file
        end
      end

      # First pass: add all skills
      all_skill_files.each do |skill_file|
        begin
          skill_data = parse_skill_file(skill_file)
          network.add_skill(
            skill_data[:name],
            trit: skill_data[:trit] || 0,
            version: skill_data[:version] || "1.0.0",
            bundle: skill_data[:bundle] || "core",
            date: skill_data[:date] || Time.now
          )
        rescue => e
          puts "Warning: Could not parse #{skill_file}: #{e.message}"
        end
      end

      # Second pass: add dependencies
      all_skill_files.each do |skill_file|
        begin
          skill_data = parse_skill_file(skill_file)
          skill_name = skill_data[:name]

          (skill_data[:related_skills] || []).each do |dep_name|
            if network.skills.key?(dep_name)
              network.add_dependency(skill_name, dep_name)
            end
          end
        rescue => e
          # Silently skip errors on second pass
        end
      end

      network
    end

    def self.parse_skill_file(path)
      content = File.read(path)
      yaml_data = {}

      # Try to extract YAML frontmatter
      if content =~ /^---\n(.*?)\n---/m
        yaml_str = Regexp.last_match(1)
        yaml_data = YAML.safe_load(yaml_str) || {}
      end

      # Fallback: extract name and trit from content
      skill_name = yaml_data['name'] || File.basename(File.dirname(path))

      # Parse trit - handle multiple formats
      raw_trit = yaml_data['trit']
      trit = case raw_trit
             when -1, '-1', 'MINUS', /^-1/
               -1
             when 1, '+1', 'PLUS', /^\+1/
               1
             when 0, 'ERGODIC', nil
               # Try to find trit in markdown content
               if content =~ /[tT]rit[:\s]*([+-]?1|0|PLUS|MINUS|ERGODIC)/i
                 case Regexp.last_match(1).upcase
                 when 'PLUS', '+1'
                   1
                 when 'MINUS', '-1'
                   -1
                 else
                   0
                 end
               else
                 0
               end
             else
               0
             end

      # Parse date
      date = if yaml_data['date']
               Time.parse(yaml_data['date'].to_s)
             else
               File.mtime(path)
             end

      {
        name: skill_name,
        trit: trit,
        version: yaml_data['version'] || "1.0.0",
        bundle: yaml_data['bundle'] || "core",
        date: date,
        related_skills: yaml_data['related_skills'] || [],
        description: yaml_data['description'] || ""
      }
    end
  end

  # ============================================================================
  # ANALYZER: Generate reports on mixing times
  # ============================================================================

  class MixingAnalyzer
    def self.analyze_and_report(network, output_file: nil)
      puts "\n" + "="*80
      puts "SKILL NETWORK MIXING TIME ANALYSIS"
      puts "="*80

      # Basic statistics
      puts "\n📊 NETWORK STATISTICS"
      puts "-" * 80
      puts "Total skills:           #{network.skills.size}"
      puts "Skill types:"
      trits = network.skills.values.map(&:trit)
      puts "  - PLUS (+1):          #{trits.count(1)}"
      puts "  - ERGODIC (0):        #{trits.count(0)}"
      puts "  - MINUS (-1):         #{trits.count(-1)}"

      # GF(3) conservation
      gf3 = network.analyze_gf3_conservation
      puts "\n🔄 GF(3) CONSERVATION LAW"
      puts "-" * 80
      puts "Sum of all trits (mod 3): #{gf3[:sum_mod_3]}"
      puts "Conservation verified:    #{gf3[:conserved] ? '✅ YES' : '❌ NO'}"
      puts "Trit distribution:        #{gf3[:ratio]}"

      # Mixing time
      puts "\n⏱️  MIXING TIME ANALYSIS"
      puts "-" * 80
      mixing_round = network.measure_mixing_time(max_rounds: 100, tolerance: 0.01)
      puts "Mixing round (convergence): #{mixing_round}"
      puts "Final entropy:              #{network.mixing_times[:final_entropy]&.round(4)}"
      puts "Converged:                  #{network.mixing_times[:converged] ? '✅ YES' : '⏳ ONGOING'}"

      # Network topology
      puts "\n🌐 NETWORK TOPOLOGY"
      puts "-" * 80
      puts "Average mixing distance:    #{network.average_mixing_distance.round(2)}"
      puts "Network diameter:           #{network.diameter}"

      # Sample propagation timeline
      puts "\n📡 INFORMATION PROPAGATION (First 5 Rounds)"
      puts "-" * 80
      network.propagation_timeline[0..4].each do |round_data|
        puts "\n  Round #{round_data[:round]}:"
        round_data[:events].group_by { |e| e[:skill] }.each do |skill, events|
          ticks = events.select { |e| e[:event] == :tick }
          receives = events.select { |e| e[:received_from] }

          clock_val = ticks.first[:clock] if ticks.first

          if receives.any?
            puts "    #{skill}: received from #{receives.map { |r| r[:received_from] }.join(', ')} → clock: #{clock_val}"
          end
        end
      end

      # Entropy convergence
      if network.mixing_times[:entropy_history]
        puts "\n📈 ENTROPY CONVERGENCE"
        puts "-" * 80
        history = network.mixing_times[:entropy_history]
        sample_rounds = [0, history.size/4, history.size/2, 3*history.size/4, history.size-1].uniq
        sample_rounds.each do |i|
          puts "  Round #{i.to_s.rjust(3)}: entropy = #{history[i].round(4)}"
        end
      end

      # JSON output
      if output_file
        json_data = network.to_json
        File.write(output_file, JSON.pretty_generate(json_data))
        puts "\n✅ Results saved to #{output_file}"
      end

      network
    end
  end
end

# ============================================================================
# DEMO: Load actual skills and measure mixing time
# ============================================================================

if __FILE__ == $0
  puts "🔧 Loading skills from music-topos..."

  # Load from music-topos (primary source)
  music_topos_dir = "/Users/bob/ies/music-topos"
  network = SkillMixingAnalysis::SkillLoader.load_from_directory(music_topos_dir)

  puts "✅ Loaded #{network.skills.size} skills"
  puts ""

  # Analyze and report
  SkillMixingAnalysis::MixingAnalyzer.analyze_and_report(
    network,
    output_file: "/Users/bob/ies/music-topos/skill_mixing_analysis.json"
  )
end
