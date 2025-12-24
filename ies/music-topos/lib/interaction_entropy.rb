# lib/interaction_entropy.rb
#
# INTERACTION ENTROPY: Every skill invocation carries deterministic color
#
# Architecture:
#   1. Hash interaction content → SHA256
#   2. Derive seed from hash → SplitMix64
#   3. Generate color at walk position → LCH
#   4. Map hue to trit → GF(3)
#   5. Track self-avoiding walk → unique path
#   6. Verify at spectral gap (1/4) → consistency check
#
# This module ensures EVERY interaction includes entropy, enabling:
#   - Deterministic replay (same content → same colors)
#   - GF(3) conservation across skill triplets
#   - Self-avoiding walk for unique interaction paths
#   - ACSet export for Julia interop
#   - DiscoHy diagram generation for Python/Hy interop

require 'digest'
require 'json'
require 'open3'
require_relative 'splitmix_ternary'
require_relative 'self_avoiding_colored_walk'

module InteractionEntropy
  # ═══════════════════════════════════════════════════════════════════════════════
  # CONSTANTS
  # ═══════════════════════════════════════════════════════════════════════════════
  
  DB_PATH = "interaction_entropy.duckdb"
  SPECTRAL_GAP = 0.25
  
  # Skill roles mapped to trits (GF(3) structure)
  SKILL_ROLES = {
    generator: { trit: 1, description: "Proposes, creates, expands" },
    coordinator: { trit: 0, description: "Bridges, transforms, mediates" },
    validator: { trit: -1, description: "Verifies, constrains, checks" }
  }.freeze
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # INTERACTION RECORD
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class Interaction
    attr_reader :id, :thread_id, :epoch, :content_hash, :seed
    attr_reader :walk_position, :color, :trit
    attr_reader :skill_name, :skill_role, :verified
    attr_accessor :result
    
    def initialize(content, thread_id: nil, epoch: nil, skill_name: nil, skill_role: nil)
      @thread_id = thread_id
      @epoch = epoch || Time.now.to_i
      @skill_name = skill_name
      @skill_role = skill_role
      
      # Derive entropy from content
      @content_hash = Digest::SHA256.hexdigest(content.to_s)
      @seed = derive_seed(@content_hash)
      @id = "I-#{@content_hash[0..15]}"
      
      # Initialize as unverified
      @verified = false
      @result = nil
    end
    
    def derive_seed(hash_str)
      # Take first 16 hex chars as 64-bit seed
      hash_str[0..15].to_i(16)
    end
    
    # Compute walk position from global walker
    def compute_walk!(walker)
      result = walker.on_interaction(@seed)
      @walk_position = result[:position]
      @color = @walk_position.color
      @trit = @walk_position.trit
      @verified = result[:verification][:verified]
      self
    end
    
    def to_h
      {
        id: @id,
        thread_id: @thread_id,
        epoch: @epoch,
        content_hash: @content_hash,
        seed: "0x#{@seed.to_s(16)}",
        walk: {
          x: @walk_position&.x,
          y: @walk_position&.y,
          color_index: @walk_position&.color_index
        },
        color: @color ? { L: @color[:L], C: @color[:C], H: @color[:H] } : nil,
        trit: @trit,
        skill: { name: @skill_name, role: @skill_role },
        verified: @verified
      }
    end
    
    def to_sql_insert
      c = @color || { L: 50.0, C: 50.0, H: 180.0 }
      wp = @walk_position || OpenStruct.new(x: 0, y: 0, color_index: 0)
      
      <<~SQL
        INSERT INTO interactions (
          interaction_id, thread_id, epoch, entropy_hash, derived_seed,
          walk_x, walk_y, walk_color_index,
          color_l, color_c, color_h, trit,
          skill_name, skill_role, verified
        ) VALUES (
          '#{@id}', 
          #{@thread_id ? "'#{@thread_id}'" : 'NULL'},
          #{@epoch},
          '#{@content_hash}',
          #{@seed},
          #{wp.x}, #{wp.y}, #{wp.color_index},
          #{c[:L].round(4)}, #{c[:C].round(4)}, #{c[:H].round(4)},
          #{@trit || 0},
          #{@skill_name ? "'#{@skill_name}'" : 'NULL'},
          #{@skill_role ? "'#{@skill_role}'" : 'NULL'},
          #{@verified}
        );
      SQL
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # ENTROPY MANAGER: Global tracker for all interactions
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class EntropyManager
    attr_reader :interactions, :walker, :triplets, :db_path
    
    def initialize(base_seed: SplitMixTernary::DEFAULT_SEED, db_path: DB_PATH)
      @base_seed = base_seed
      @db_path = db_path
      @walker = SelfAvoidingColoredWalk::InteractionWalker.new(base_seed)
      @interactions = []
      @triplets = []
      @tripartite = SplitMixTernary::TripartiteStreams.new(base_seed)
      @epoch = 0
    end
    
    # Record an interaction with entropy
    def record!(content, skill_name: nil, skill_role: nil, thread_id: nil)
      @epoch += 1
      
      interaction = Interaction.new(
        content,
        thread_id: thread_id,
        epoch: @epoch,
        skill_name: skill_name,
        skill_role: skill_role
      )
      
      # Compute walk position (this is where entropy becomes color)
      interaction.compute_walk!(@walker)
      
      @interactions << interaction
      
      # Check if we have a new triplet for GF(3)
      if @interactions.size >= 3 && (@interactions.size % 3 == 0)
        last_three = @interactions.last(3)
        triplet = form_triplet(last_three)
        @triplets << triplet
      end
      
      interaction
    end
    
    # Wrap a skill invocation with entropy
    def with_entropy(content, skill_name:, skill_role:, thread_id: nil, &block)
      interaction = record!(content, 
                            skill_name: skill_name, 
                            skill_role: skill_role,
                            thread_id: thread_id)
      
      # Execute the skill block with interaction context
      result = yield(interaction) if block_given?
      interaction.result = result
      
      { interaction: interaction, result: result }
    end
    
    def form_triplet(interactions)
      trits = interactions.map(&:trit)
      trit_sum = trits.sum
      gf3_residue = ((trit_sum % 3) + 3) % 3
      
      {
        interactions: interactions.map(&:id),
        trits: trits,
        trit_sum: trit_sum,
        gf3_residue: gf3_residue,
        gf3_conserved: gf3_residue == 0
      }
    end
    
    # Get conservation stats
    def gf3_stats
      conserved = @triplets.count { |t| t[:gf3_conserved] }
      {
        total_triplets: @triplets.size,
        conserved: conserved,
        violations: @triplets.size - conserved,
        conservation_rate: @triplets.empty? ? 1.0 : conserved.to_f / @triplets.size
      }
    end
    
    # Get walk stats
    def walk_stats
      @walker.walk.spectral_summary
    end
    
    # Persist to DuckDB
    def persist!(db_path: @db_path)
      sql_statements = []
      
      # Schema
      sql_statements << File.read(File.expand_path('../db/interaction_entropy_schema.sql', __dir__)) rescue ""
      
      # Interactions
      @interactions.each do |interaction|
        sql_statements << interaction.to_sql_insert
      end
      
      # Triplets
      @triplets.each_with_index do |triplet, i|
        sql_statements << <<~SQL
          INSERT INTO interaction_triplets (
            triplet_id, 
            interaction_1_id, interaction_2_id, interaction_3_id,
            trit_1, trit_2, trit_3
          ) VALUES (
            'T-#{i}',
            '#{triplet[:interactions][0]}',
            '#{triplet[:interactions][1]}',
            '#{triplet[:interactions][2]}',
            #{triplet[:trits][0]},
            #{triplet[:trits][1]},
            #{triplet[:trits][2]}
          );
        SQL
      end
      
      # Execute via DuckDB CLI
      sql = sql_statements.join("\n")
      stdout, stderr, status = Open3.capture3("duckdb #{db_path}", stdin_data: sql)
      
      if status.success?
        { success: true, db_path: db_path, interactions: @interactions.size, triplets: @triplets.size }
      else
        { success: false, error: stderr }
      end
    end
    
    # Export for Julia ACSet
    def to_acset_json
      {
        schema: "InteractionEntropy",
        objects: {
          Interaction: @interactions.map(&:to_h),
          Color: @interactions.map { |i| i.color }.compact.uniq,
          Triplet: @triplets
        },
        morphisms: {
          interaction_to_color: @interactions.map.with_index { |i, idx| 
            { src: idx, tgt: i.color } 
          },
          triplet_to_interactions: @triplets.map.with_index { |t, idx|
            { src: idx, tgt: t[:interactions] }
          }
        }
      }
    end
    
    # Export for DiscoHy diagram
    def to_discopy_diagram
      boxes = @interactions.map do |i|
        {
          name: i.skill_name || "interaction",
          dom: i.skill_role == :generator ? ["Input"] : ["State"],
          cod: i.skill_role == :validator ? ["Output"] : ["State"],
          color: i.color
        }
      end
      
      wires = @interactions.each_cons(2).map do |src, tgt|
        {
          src: src.id,
          tgt: tgt.id,
          type: "State",
          trit: tgt.trit
        }
      end
      
      { type: "monoidal_diagram", boxes: boxes, wires: wires }
    end
    
    def summary
      {
        epoch: @epoch,
        interactions: @interactions.size,
        triplets: @triplets.size,
        gf3: gf3_stats,
        walk: walk_stats,
        base_seed: "0x#{@base_seed.to_s(16)}"
      }
    end
    
    def to_s
      s = summary
      <<~SUMMARY
        ╔═══════════════════════════════════════════════════════════════════╗
        ║  INTERACTION ENTROPY MANAGER                                     ║
        ╚═══════════════════════════════════════════════════════════════════╝
        
        Base Seed: #{s[:base_seed]}
        Epoch: #{s[:epoch]}
        
        ─── Interactions ───
          Total: #{s[:interactions]}
          Triplets formed: #{s[:triplets]}
        
        ─── GF(3) Conservation ───
          Conserved: #{s[:gf3][:conserved]} / #{s[:gf3][:total_triplets]}
          Violations: #{s[:gf3][:violations]}
          Rate: #{(s[:gf3][:conservation_rate] * 100).round(1)}%
        
        ─── Self-Avoiding Walk ───
          Steps: #{s[:walk][:steps]}
          Self-avoiding: #{s[:walk][:is_self_avoiding] ? '✓' : '✗'}
          Violations caught: #{s[:walk][:violations_caught]}
          Spectral gap: #{s[:walk][:spectral_gap]}
        
        ═══════════════════════════════════════════════════════════════════
      SUMMARY
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # SKILL WRAPPER: Enforce entropy on every skill call
  # ═══════════════════════════════════════════════════════════════════════════════
  
  class SkillWrapper
    attr_reader :manager, :skill_name, :skill_role, :trit
    
    def initialize(skill_name:, skill_role:, manager: nil)
      @skill_name = skill_name
      @skill_role = skill_role
      @trit = SKILL_ROLES[skill_role][:trit]
      @manager = manager || EntropyManager.new
    end
    
    # Invoke skill with mandatory entropy capture
    def invoke(input, thread_id: nil, &block)
      content = { skill: @skill_name, role: @skill_role, input: input }
      
      @manager.with_entropy(
        content.to_json,
        skill_name: @skill_name,
        skill_role: @skill_role,
        thread_id: thread_id,
        &block
      )
    end
    
    # Class method to create a wrapped skill triad
    def self.triad(generator:, coordinator:, validator:, manager: nil)
      m = manager || EntropyManager.new
      {
        generator: SkillWrapper.new(skill_name: generator, skill_role: :generator, manager: m),
        coordinator: SkillWrapper.new(skill_name: coordinator, skill_role: :coordinator, manager: m),
        validator: SkillWrapper.new(skill_name: validator, skill_role: :validator, manager: m),
        manager: m
      }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════════════════════
  # MODULE METHODS
  # ═══════════════════════════════════════════════════════════════════════════════
  
  def self.new_manager(seed: SplitMixTernary::DEFAULT_SEED, db_path: DB_PATH)
    EntropyManager.new(base_seed: seed, db_path: db_path)
  end
  
  def self.wrap_skill(name:, role:, manager: nil)
    SkillWrapper.new(skill_name: name, skill_role: role, manager: manager)
  end
  
  def self.skill_triad(generator:, coordinator:, validator:, manager: nil)
    SkillWrapper.triad(generator: generator, coordinator: coordinator, validator: validator, manager: manager)
  end
  
  def self.demo(seed: 0x42D)
    puts "╔═══════════════════════════════════════════════════════════════════╗"
    puts "║  INTERACTION ENTROPY: Skills with Deterministic Colors           ║"
    puts "╚═══════════════════════════════════════════════════════════════════╝"
    puts
    
    # Create skill triad
    triad = skill_triad(
      generator: "rubato-composer",
      coordinator: "glass-bead-game", 
      validator: "bisimulation-game"
    )
    
    puts "Skill Triad:"
    puts "  Generator (+1): #{triad[:generator].skill_name}"
    puts "  Coordinator (0): #{triad[:coordinator].skill_name}"
    puts "  Validator (-1): #{triad[:validator].skill_name}"
    puts
    
    # Simulate 9 interactions (3 triplets)
    puts "─── Recording Interactions ───"
    9.times do |i|
      role = [:generator, :coordinator, :validator][i % 3]
      skill = triad[role]
      
      result = skill.invoke("Input #{i + 1}") do |interaction|
        "Processed by #{interaction.skill_name} at walk(#{interaction.walk_position.x}, #{interaction.walk_position.y})"
      end
      
      interaction = result[:interaction]
      trit_char = interaction.trit == 1 ? '+' : (interaction.trit == -1 ? '-' : '0')
      puts "  #{i + 1}. [#{trit_char}] #{interaction.skill_name}: H=#{interaction.color[:H].round(1)}° at (#{interaction.walk_position.x}, #{interaction.walk_position.y})"
    end
    puts
    
    # Show summary
    manager = triad[:manager]
    puts manager.to_s
    
    # Show triplet details
    puts "─── GF(3) Triplets ───"
    manager.triplets.each_with_index do |t, i|
      status = t[:gf3_conserved] ? '✓' : '✗'
      puts "  #{i + 1}. trits=[#{t[:trits].join(', ')}] sum=#{t[:trit_sum]} #{status}"
    end
    puts
    
    # Export formats
    puts "─── Export Formats ───"
    puts "  ACSet JSON: #{manager.to_acset_json.to_json[0..100]}..."
    puts "  DisCoPy: #{manager.to_discopy_diagram[:boxes].size} boxes, #{manager.to_discopy_diagram[:wires].size} wires"
    puts
    
    manager
  end
end

if __FILE__ == $0
  InteractionEntropy.demo
end
