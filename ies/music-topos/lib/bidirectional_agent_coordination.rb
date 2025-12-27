# lib/bidirectional_agent_coordination.rb
#
# BIDIRECTIONAL AGENT-SKILL COORDINATION LAYER
# ═════════════════════════════════════════════════════════════════════════════
#
# Bridges the bidirectional_skill_traversal system with agent-o-rama.
# 
# Architecture:
# ┌────────────────────────────────────────┐
# │     Agent-O-Rama (Barton Surrogate)    │
# └─────────────────┬──────────────────────┘
#                   │
#        ┌──────────▼──────────┐
#        │  BidirectionalAgent │
#        │   Coordinator       │
#        └──────────┬──────────┘
#                   │
#    ┌──────────────┼──────────────┐
#    │              │              │
#    ▼              ▼              ▼
# SkillCircuit  Concept      Feedback
#               Layer        Loop
#
# Key insight: Not only do agents learn from skills,
# skills learn from agents, and agents learn from other agents.
# All bidirectionally coupled.

require_relative 'bidirectional_skill_traversal'

module BidirectionalAgentCoordination
  
  class AgentSkillBridge
    #
    # Mediates between Agent-O-Rama and the living skill ecosystem.
    # The agent learns what skills can do.
    # The skills learn what the agent values.
    #
    
    attr_reader :agent_id, :ecosystem, :agent_specialization, :interaction_log
    
    def initialize(agent_id:, num_skills: 3)
      @agent_id = agent_id
      @ecosystem = BidirectionalSkillTraversal::LivingSkillEcosystem.new
      @agent_specialization = {}  # What this agent has learned to value
      @interaction_log = []
      @effectiveness_threshold = 0.6
      
      # Create initial skills unique to this agent
      num_skills.times do |i|
        skill_name = "agent_#{agent_id}_skill_#{i}"
        @ecosystem.create_skill(name: skill_name)
      end
      
      @created_at = Time.now
    end
    
    def agent_requests_skill(skill_name:, context:)
      #
      # Agent-O-Rama asks: "Which skill should I use here?"
      # Returns not just the skill, but a prediction of its effectiveness.
      #
      
      skill = @ecosystem.skills[skill_name]
      return nil unless skill
      
      # Prepare inputs: context as binary features
      inputs = extract_binary_features(context)
      
      # Execute skill circuit
      execution = skill.execute(inputs)
      
      # Track this request (agent learning what skill does)
      request_record = {
        time: Time.now,
        agent_id: @agent_id,
        skill_name: skill_name,
        context: context,
        predicted_output: execution[:final_output],
        execution_path: execution[:execution_path],
        confidence: predict_effectiveness(skill_name, context)
      }
      
      @interaction_log << request_record
      
      request_record
    end
    
    def agent_observes_skill_outcome(skill_name:, actual_effectiveness:, feedback_reason:)
      #
      # After using a skill, the agent observes how well it worked.
      # This feedback rewires the skill and updates agent's understanding.
      #
      
      skill = @ecosystem.skills[skill_name]
      return nil unless skill
      
      env_feedback = {
        effectiveness: actual_effectiveness,
        feedback_signal: "agent_#{@agent_id}_observation",
        reason: feedback_reason
      }
      
      # Skill rewires based on feedback
      rewire_result = @ecosystem.skill_interaction(
        skill_name: skill_name,
        inputs: [rand, rand],  # Dummy inputs for now
        env_feedback: env_feedback
      )
      
      # Agent updates its specialization
      if actual_effectiveness > @effectiveness_threshold
        @agent_specialization[skill_name] = {
          confidence: actual_effectiveness,
          context_pattern: feedback_reason,
          last_updated: Time.now
        }
      end
      
      rewire_result
    end
    
    def agent_self_improves
      #
      # Agent meta-learns: "Based on skill outcomes, what should I focus on?"
      # The agent's concept layer re-evaluates its understanding.
      #

      # Analyze which skills worked best (from agent_specialization which tracks actual outcomes)
      specializations = {}
      @agent_specialization.each do |skill_name, spec_data|
        specializations[skill_name] = spec_data[:confidence]
      end

      # If no specialization yet, return neutral learning trajectory
      if specializations.empty?
        return {
          agent_id: @agent_id,
          specializations: {},
          dominant_skill: nil,
          dominant_effectiveness: nil,
          learning_trajectory: false
        }
      end

      # Most specialized skill emerges
      best_skill = specializations.max_by { |_, rate| rate }

      {
        agent_id: @agent_id,
        specializations: specializations,
        dominant_skill: best_skill&.first,
        dominant_effectiveness: best_skill&.last,
        learning_trajectory: specializations.length > 0
      }
    end
    
    def coordinate_with_other_agents(other_bridges:)
      #
      # Agents learn from each other.
      # Share what skills worked, discover complementary specializations.
      # This is bidirectional: each agent teaches and learns.
      #
      
      shared_knowledge = []
      
      other_bridges.each do |other|
        next if other.agent_id == @agent_id
        
        # What did they learn that I didn't try?
        their_skills = other.ecosystem.skills.keys
        my_skills = @ecosystem.skills.keys
        
        complementary = their_skills - my_skills
        shared_skills = their_skills & my_skills
        
        # Cross-agent learning
        shared_knowledge << {
          learned_from: other.agent_id,
          complementary_skills: complementary,
          shared_skills: shared_skills,
          their_specialization: other.agent_specialization,
          knowledge_transfer: true
        }
      end
      
      shared_knowledge
    end
    
    def status
      {
        agent_id: @agent_id,
        created_at: @created_at,
        total_skills: @ecosystem.skills.length,
        total_interactions: @interaction_log.length,
        specialization: @agent_specialization,
        ecosystem_state: @ecosystem.ecosystem_state
      }
    end
    
    private
    
    def extract_binary_features(context)
      # Convert context hash to binary features
      context.values.map { |v| v.is_a?(Numeric) ? v : (v ? 1 : 0) }
    end
    
    def predict_effectiveness(skill_name, context)
      # Predict how well this skill will work in this context
      if @agent_specialization[skill_name]
        @agent_specialization[skill_name][:confidence]
      else
        0.5  # Default uncertainty
      end
    end
  end
  
  class MultiAgentEcosystem
    #
    # Community of agents, each with their own bidirectional skill evolution.
    # Agents coordinate, compete, and co-evolve.
    # Creates emergent organizational structures.
    #
    
    attr_reader :agents, :coordination_history
    
    def initialize(num_agents: 3, skills_per_agent: 2)
      @agents = {}
      @coordination_history = []
      
      num_agents.times do |i|
        agent_id = "agent_#{i}"
        @agents[agent_id] = AgentSkillBridge.new(
          agent_id: agent_id,
          num_skills: skills_per_agent
        )
      end
    end
    
    def run_coordination_round
      #
      # Each agent acts, learns, and learns from peers.
      #
      
      round_results = {}
      
      # Phase 1: Each agent uses their skills
      @agents.each do |agent_id, bridge|
        round_results[agent_id] = bridge.agent_self_improves
      end
      
      # Phase 2: Agents learn from each other
      agent_bridges = @agents.values
      agent_bridges.each do |bridge|
        others = agent_bridges.reject { |b| b.agent_id == bridge.agent_id }
        knowledge_transfers = bridge.coordinate_with_other_agents(other_bridges: others)
        round_results[bridge.agent_id][:knowledge_transfers] = knowledge_transfers
      end
      
      # Record this coordination event
      @coordination_history << {
        time: Time.now,
        round_results: round_results,
        ecosystem_diversity: measure_ecosystem_diversity
      }
      
      round_results
    end
    
    def ecosystem_status
      {
        num_agents: @agents.length,
        total_coordination_rounds: @coordination_history.length,
        agent_statuses: @agents.transform_values { |b| b.status },
        ecosystem_diversity: measure_ecosystem_diversity,
        irreducible: @agents.length > 2 && @coordination_history.length > 3
      }
    end
    
    private
    
    def measure_ecosystem_diversity
      # Measure how specialized agents have become
      specializations = @agents.values.map { |b| b.agent_specialization.keys.length }
      return 0.0 if specializations.empty?
      
      mean = specializations.sum.to_f / specializations.length
      variance = specializations.map { |s| (s - mean) ** 2 }.sum / specializations.length
      Math.sqrt(variance)
    end
  end
end

# ═════════════════════════════════════════════════════════════════════════════
# DEMO: Multi-Agent Bidirectional Coordination
# ═════════════════════════════════════════════════════════════════════════════

if __FILE__ == $0
  puts "🤖 Starting Multi-Agent Bidirectional Coordination System...\n\n"
  
  # Create ecosystem of 3 agents, each with 2 skills
  ecosystem = BidirectionalAgentCoordination::MultiAgentEcosystem.new(
    num_agents: 3,
    skills_per_agent: 2
  )
  
  puts "✓ Created 3 agents with bidirectional skill networks"
  puts "✓ Each agent has 2 unique skills + concept hierarchies\n\n"
  
  # Simulate 3 coordination rounds
  3.times do |round|
    puts "═" * 70
    puts "COORDINATION ROUND #{round + 1}"
    puts "═" * 70
    
    results = ecosystem.run_coordination_round
    
    results.each do |agent_id, result|
      puts "\n#{agent_id}:"
      puts "  Specializations: #{result[:specializations]}"
      puts "  Dominant Skill: #{result[:dominant_skill]}"
      puts "  Learning Trajectory: #{result[:learning_trajectory]}"
      
      knowledge_transfers = result[:knowledge_transfers] || []
      if knowledge_transfers.any?
        puts "  Knowledge Transfers: #{knowledge_transfers.length} from peers"
      end
    end
  end
  
  puts "\n" + "=" * 70
  puts "ECOSYSTEM STATE (Irreducible Living Structure)"
  puts "=" * 70
  
  status = ecosystem.ecosystem_status
  puts "Agents: #{status[:num_agents]}"
  puts "Coordination Rounds: #{status[:total_coordination_rounds]}"
  puts "Ecosystem Diversity: #{status[:ecosystem_diversity].round(3)}"
  puts "Irreducible Structure Emerged: #{status[:irreducible]}"
  
  puts "\n🌱 AGENT SPECIALIZATIONS:"
  status[:agent_statuses].each do |agent_id, agent_status|
    puts "\n#{agent_id}:"
    puts "  Total Skills: #{agent_status[:total_skills]}"
    puts "  Total Interactions: #{agent_status[:total_interactions]}"
    puts "  Specialization: #{agent_status[:specialization].keys.join(', ') || 'None yet'}"
  end
end
