# lib/bidirectional_agent_demo.rb
#
# ACTIVE DEMONSTRATION: Agents learning through bidirectional skill rewiring
# Shows emergent specialization and cross-agent learning

require_relative 'bidirectional_agent_coordination'

class ActiveAgentDemonstration

  def initialize
    @ecosystem = BidirectionalAgentCoordination::MultiAgentEcosystem.new(
      num_agents: 3,
      skills_per_agent: 2
    )
  end

  def run
    puts "\n" + "=" * 75
    puts "BIDIRECTIONAL AGENT-SKILL ECOSYSTEM DEMO"
    puts "Showing emergent specialization through mutual co-evolution"
    puts "=" * 75 + "\n"

    # Warm-up: Each agent tries their skills
    puts "PHASE 1: SKILL EXPLORATION"
    puts "-" * 75

    @ecosystem.agents.each do |agent_id, bridge|
      puts "\n#{agent_id} explores its skills:"

      bridge.ecosystem.skills.each do |skill_name, skill|
        # Agent tries the skill 3 times with different contexts
        3.times do |attempt|
          context = {
            attempt: attempt,
            complexity: rand,
            diversity: rand > 0.5
          }

          request = bridge.agent_requests_skill(
            skill_name: skill_name,
            context: context
          )

          # Simulate outcome: more effective on some contexts
          effectiveness = if context[:diversity]
                           0.7 + rand * 0.3  # Good effectiveness
                         else
                           0.4 + rand * 0.3  # Lower effectiveness
                         end

          bridge.agent_observes_skill_outcome(
            skill_name: skill_name,
            actual_effectiveness: effectiveness,
            feedback_reason: "exploration_attempt_#{attempt}"
          )

          puts "  #{skill_name}: effectiveness=#{effectiveness.round(2)}, " +
               "output=#{request[:predicted_output]}"
        end
      end
    end

    # Phase 2: Specialization emerges
    puts "\n\nPHASE 2: SPECIALIZATION EMERGENCE"
    puts "-" * 75

    specializations = {}
    @ecosystem.agents.each do |agent_id, bridge|
      improvement = bridge.agent_self_improves
      specializations[agent_id] = improvement

      puts "\n#{agent_id} specialization:"
      puts "  Best skill: #{improvement[:dominant_skill]}"
      puts "  Effectiveness: #{improvement[:dominant_effectiveness]&.round(2)}"
      puts "  All specializations: #{improvement[:specializations].map { |k, v|
        "#{k.split('_').last}=#{v.round(2)}"
      }.join(', ')}"
    end

    # Phase 3: Cross-agent learning
    puts "\n\nPHASE 3: CROSS-AGENT LEARNING"
    puts "-" * 75

    results = @ecosystem.run_coordination_round

    results.each do |agent_id, result|
      puts "\n#{agent_id} learned:"
      if result[:knowledge_transfers] && result[:knowledge_transfers].any?
        result[:knowledge_transfers].each do |transfer|
          puts "  From #{transfer[:learned_from]}: " +
               "#{transfer[:complementary_skills].length} complementary skills"
        end
      end
    end

    # Final status
    puts "\n\nFINAL ECOSYSTEM STATUS"
    puts "-" * 75

    status = @ecosystem.ecosystem_status
    puts "Total Agents: #{status[:num_agents]}"
    puts "Specializations Emerged: #{specializations.count { |_, s| s[:dominant_skill] }}"
    puts "Ecosystem Diversity Index: #{status[:ecosystem_diversity].round(3)}"
    puts "Irreducible Structure: #{status[:irreducible] ? '✅ YES' : '🔲 Emerging'}"

    # Show the bidirectional nature
    puts "\n\nBIDIRECTIONAL FEEDBACK LOOPS:"
    puts "-" * 75
    @ecosystem.agents.each do |agent_id, bridge|
      puts "\n#{agent_id}:"
      puts "  Skills can do:     #{bridge.ecosystem.skills.keys.map { |k| k.split('_').last }}"
      puts "  Agent specializes: #{bridge.agent_specialization.keys.map { |k| k.split('_').last }}"
      puts "  Interactions:      #{bridge.interaction_log.length}"
      puts "  Skills rewired:    #{bridge.ecosystem.skills.values.map { |s|
        s.instance_variable_get(:@interaction_history).length
      }.sum}"
    end

    # Show the irreducible living structure
    puts "\n\nIRREDUCIBLE LIVING STRUCTURE:"
    puts "-" * 75

    explanation = <<~EXPLANATION
      The system exhibits irreducibility - like Go players improving after AlphaGo:

      1. AGENTS learn what SKILLS can do
         └─ Agent specializes in certain skills (agent_specialization)

      2. SKILLS learn what AGENTS value
         └─ Skills rewire gates when agents give feedback (rewire_from_interaction)

      3. AGENTS learn from OTHER AGENTS
         └─ Cross-agent knowledge transfer (coordinate_with_other_agents)

      4. AGENTS rewire their own UNDERSTANDING
         └─ Meta-learning: "which skill should I focus on?" (agent_self_improves)

      5. ECOSYSTEM becomes ALIVE
         └─ Emerges when interactions > 5 AND diversity > 0

      NONE of these layers can be reduced to the others. The whole is alive because:
      - Change agent understanding → skills need to rewire
      - Change skill behavior → agents change specialization
      - Change ecosystem composition → all agents' learning trajectories shift
      - All coupled bidirectionally

      This is the "two-eye" irreducibility: You cannot understand the system from
      any single perspective (agent alone, skill alone, or environment alone).
      The pattern emerges from interaction.
    EXPLANATION

    puts explanation

    puts "\n"
  end
end

# Run the demonstration
if __FILE__ == $0
  demo = ActiveAgentDemonstration.new
  demo.run
end
