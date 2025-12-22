# Interaction ACSet Schema: Recording This Session
# Generated: 2025-12-22T22:30:00Z
# Purpose: Store multi-agent, multi-skill interactions in categorical form

using Catlab.CategoricalAlgebra

"""
SchInteraction: Master schema for interaction recording

Objects:
  - Agent: AI system or human (codex, claude, user, etc)
  - Skill: Loaded capability (acsets, alife, unworlding-involution, etc)
  - Action: Operation performed (load, invoke, compute, disperse)
  - State: System state snapshot (before/after)
  - Epoch: Timestep in session
  - Message: Communication between agents
  - Bead: Glass bead game concept
  - World: Possible world (world-hopping)
  - Trit: GF(3) value {-1, 0, +1}

Morphisms:
  - agent_performs: Agent → Action
  - action_uses_skill: Action → Skill
  - action_changes_state: State → State
  - state_at_epoch: State → Epoch
  - message_from: Agent → Message
  - message_to: Agent → Message
  - bead_of_game: Bead → Game
  - world_hop: World → World
  - trit_of_entity: Trit → [Agent|Skill|Action]
"""

@present SchInteraction(FreeSchema) begin
  # Core entities
  Agent::Ob
  Skill::Ob
  Action::Ob
  State::Ob
  Epoch::Ob
  Message::Ob

  # Theory entities
  Bead::Ob
  Game::Ob
  World::Ob
  Trit::Ob

  # Morphisms: who does what
  agent_performs::Hom(Action, Agent)
  action_uses_skill::Hom(Action, Skill)

  # Morphisms: state evolution
  action_changes_state::Hom(Action, State)
  state_before::Hom(State, State)
  state_after::Hom(State, State)
  state_at_epoch::Hom(State, Epoch)

  # Morphisms: communication
  message_from::Hom(Message, Agent)
  message_to::Hom(Message, Agent)
  message_uses_skill::Hom(Message, Skill)

  # Morphisms: theory integration
  bead_of_game::Hom(Bead, Game)
  action_invokes_bead::Hom(Action, Bead)

  # Morphisms: world hopping
  world_hop::Hom(World, World)
  epoch_world::Hom(Epoch, World)

  # Morphisms: GF(3) coloring
  agent_trit::Hom(Agent, Trit)
  skill_trit::Hom(Skill, Trit)
  action_trit::Hom(Action, Trit)

  # Constraints: Actions compose
  # action1 → state1 → state2 ← action2

  # Constraints: Messages preserve trit sum
  # trit(from_agent) + trit(to_agent) + trit(message) ≡ 0 (mod 3)
end

@acset_type Interaction(SchInteraction, index=[:agent_performs, :action_uses_skill])

"""
Build initial interaction ACSet for session
"""
function build_session_acset()
  session = Interaction()

  # Add agents (8 skill loaders)
  agents = [:claude_code, :amp, :codex, :cursor, :explorer, :builder, :reviewer, :keeper]
  agent_ids = add_parts!(session, :Agent, length(agents))

  # Add skills (8 loaded)
  skills = [:acsets, :alife, :unworlding_involution, :glass_bead_game,
            :gay_mcp, :world_hopping, :algorithmic_art, :bisimulation_game]
  skill_ids = add_parts!(session, :Skill, length(skills))

  # Add epochs (timesteps)
  n_epochs = 100  # Allocate space
  epoch_ids = add_parts!(session, :Epoch, n_epochs)

  # Add trits for GF(3)
  trit_minus_1 = add_part!(session, :Trit)  # MINUS
  trit_0 = add_part!(session, :Trit)        # ERGODIC
  trit_plus_1 = add_part!(session, :Trit)   # PLUS

  # Assign agent trits (3 agents per trit)
  agent_trit_map = Dict(
    1 => trit_plus_1,    # claude_code: PLUS
    2 => trit_plus_1,    # amp: PLUS
    3 => trit_0,         # codex: ERGODIC
    4 => trit_0,         # cursor: ERGODIC
    5 => trit_minus_1,   # explorer: MINUS
    6 => trit_minus_1,   # builder: MINUS
    7 => trit_0,         # reviewer: ERGODIC
    8 => trit_plus_1,    # keeper: PLUS
  )

  # Set agent trits
  for (agent_id, trit_id) in agent_trit_map
    set_subpart!(session, agent_id, :agent_trit, trit_id)
  end

  # Assign skill trits
  skill_trit_map = Dict(
    1 => trit_0,         # acsets: ERGODIC (neutral, foundational)
    2 => trit_plus_1,    # alife: PLUS (emergence, generation)
    3 => trit_0,         # unworlding_involution: ERGODIC (self-inverse)
    4 => trit_0,         # glass_bead_game: ERGODIC (synthesis)
    5 => trit_plus_1,    # gay_mcp: PLUS (generation, colors)
    6 => trit_0,         # world_hopping: ERGODIC (navigation)
    7 => trit_plus_1,    # algorithmic_art: PLUS (creation)
    8 => trit_0,         # bisimulation_game: ERGODIC (verification)
  )

  for (skill_id, trit_id) in skill_trit_map
    set_subpart!(session, skill_id, :skill_trit, trit_id)
  end

  # Add worlds for world-hopping
  worlds = add_parts!(session, :World, 8)

  # Create world chain
  for i in 1:7
    set_subpart!(session, i, :world_hop, i + 1)
  end

  # Bind first epoch to first world
  set_subpart!(session, 1, :epoch_world, 1)

  return session, agent_ids, skill_ids, epoch_ids, agent_trit_map, skill_trit_map
end

"""
Log action: agent uses skill in epoch
"""
function log_action!(session::Interaction, agent_id, skill_id, action_name, epoch_id)
  action_id = add_part!(session, :Action)

  # Record relationships
  set_subpart!(session, action_id, :agent_performs, agent_id)
  set_subpart!(session, action_id, :action_uses_skill, skill_id)
  set_subpart!(session, action_id, :state_at_epoch, epoch_id)

  # Compute action trit = agent_trit + skill_trit (preserves sum)
  agent_trit_id = subpart(session, agent_id, :agent_trit)
  skill_trit_id = subpart(session, skill_id, :skill_trit)

  # Mapping: trit ID → value: 1 → -1, 2 → 0, 3 → +1
  trit_value(id) = (id == 1) ? -1 : ((id == 2) ? 0 : 1)
  trit_id(val) = (val == -1) ? 1 : ((val == 0) ? 2 : 3)

  agent_val = trit_value(agent_trit_id)
  skill_val = trit_value(skill_trit_id)

  # GF(3) arithmetic: compute result modulo 3
  action_val = mod(agent_val + skill_val, 3)

  # Convert back to {-1, 0, 1} range
  action_val_normalized = (action_val == 0) ? 0 : ((action_val == 1) ? 1 : -1)

  action_trit_id = trit_id(action_val_normalized)
  set_subpart!(session, action_id, :action_trit, action_trit_id)

  return action_id
end

"""
Verify GF(3) conservation in current epoch
"""
function verify_gf3_conservation(session::Interaction, epoch_id)
  # Gather all actions in this epoch
  actions = filter(1:nparts(session, :Action)) do aid
    subpart(session, aid, :state_at_epoch) == epoch_id
  end

  # Collect trits
  trits = []
  for action_id in actions
    trit_id = subpart(session, action_id, :action_trit)
    # Mapping: 1 → -1, 2 → 0, 3 → +1
    val = (trit_id == 1) ? -1 : ((trit_id == 2) ? 0 : 1)
    push!(trits, val)
  end

  sum_trits = sum(trits)
  conserved = (sum_trits % 3) == 0

  return conserved, trits, sum_trits
end

"""
Export interaction log as JSON for visualization
"""
function export_to_json(session::Interaction, filename)
  n_agents = nparts(session, :Agent)
  n_skills = nparts(session, :Skill)
  n_actions = nparts(session, :Action)

  data = Dict(
    :agents => n_agents,
    :skills => n_skills,
    :actions => n_actions,
    :timestamp => string(now()),
    :gf3_conservation => "pending",
    :schema => "SchInteraction"
  )

  open(filename, "w") do io
    JSON.print(io, data)
  end
end

# Initialize session
println(repeat("═", 70))
println("ACSET INTERACTION LOGGING INITIALIZED")
println(repeat("═", 70))

session, agents, skills, epochs, agent_trits, skill_trits = build_session_acset()

println("\n✓ Schema: SchInteraction")
println("✓ Agents: $(length(agents))")
println("✓ Skills: $(length(skills))")
println("✓ Epochs allocated: $(length(epochs))")
println("\n Agent → Trit mapping:")
agent_names = [:claude_code, :amp, :codex, :cursor, :explorer, :builder, :reviewer, :keeper]
for (i, name) in enumerate(agent_names)
  trit_val = agent_trits[i]
  trit_name = trit_val == 1 ? "MINUS(-1)" : (trit_val == 2 ? "ERGODIC(0)" : "PLUS(+1)")
  println("  $name → $trit_name")
end

println("\n Skill → Trit mapping:")
skill_names = [:acsets, :alife, :unworlding_involution, :glass_bead_game,
               :gay_mcp, :world_hopping, :algorithmic_art, :bisimulation_game]
for (i, name) in enumerate(skill_names)
  trit_val = skill_trits[i]
  trit_name = trit_val == 1 ? "MINUS(-1)" : (trit_val == 2 ? "ERGODIC(0)" : "PLUS(+1)")
  println("  $name → $trit_name")
end

println("\n GF(3) Balance Check:")
trit_sum = sum(values(agent_trits)) + sum(values(skill_trits))
agent_sum = sum(values(agent_trits))
skill_sum = sum(values(skill_trits))
println("  Agent trits sum: $agent_sum")
println("  Skill trits sum: $skill_sum")
println("  Total: $trit_sum")
println("  Conserved: $((trit_sum % 3) == 0 ? "✓" : "✗")")

println("\n" * repeat("═", 70))
println("Ready to log interactions. Call log_action!() to record.")
println(repeat("═", 70))
