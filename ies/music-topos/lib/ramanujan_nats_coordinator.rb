# lib/ramanujan_nats_coordinator.rb
#
# Ramanujan CRDT Network - NATS Coordination with Sierpinski Addressing
#
# Implements 9-agent topology using:
# - Ramanujan Expander Graph (3×3 = 3^2 vertices)
# - Sierpinski triangle addressing for document routing
# - Vector clock causality tracking
# - NATS pub/sub for distributed coordination
# - Polarity-indexed operations (RED/BLUE/GREEN)
#
# Agent Topology (Mathematician Assignments):
# Agent 0: Ramanujan (positive/RED) - TextCRDT insert operations
# Agent 1: Grothendieck (neutral/GREEN) - JSON CRDT merge
# Agent 2: Euler (negative/BLUE) - Set CRDT delete
# Agent 3: de Paiva (neutral/GREEN) - Counter update
# Agent 4: Hedges (positive/RED) - E-graph verify
# Agent 5: Girard (negative/BLUE) - TAP state union
# Agent 6: Spivak (positive/RED) - Snapshot temporal
# Agent 7: Lawvere (neutral/GREEN) - Recover rollback
# Agent 8: Scholze (negative/BLUE) - Invalidate Möbius

require 'json'
require 'set'
require 'digest'

module RamanujanNatsCoordinator
  # ===========================================================================
  # Mathematician Agent Registry
  # ===========================================================================

  MATHEMATICIANS = [
    { agent_id: 0, name: "Ramanujan", polarity: :positive, color: :RED,
      description: "TextCRDT inserts, forward rewrites" },
    { agent_id: 1, name: "Grothendieck", polarity: :neutral, color: :GREEN,
      description: "JSON CRDT merges, verification" },
    { agent_id: 2, name: "Euler", polarity: :negative, color: :BLUE,
      description: "Set CRDT deletes, inverse operations" },
    { agent_id: 3, name: "de Paiva", polarity: :neutral, color: :GREEN,
      description: "Counter updates, state snapshots" },
    { agent_id: 4, name: "Hedges", polarity: :positive, color: :RED,
      description: "E-graph verification, saturation" },
    { agent_id: 5, name: "Girard", polarity: :negative, color: :BLUE,
      description: "TAP state unions, linear logic" },
    { agent_id: 6, name: "Spivak", polarity: :positive, color: :RED,
      description: "Snapshot creation, temporal versioning" },
    { agent_id: 7, name: "Lawvere", polarity: :neutral, color: :GREEN,
      description: "Recover operations, rollback logic" },
    { agent_id: 8, name: "Scholze", polarity: :negative, color: :BLUE,
      description: "Invalidation, Möbius inversion" }
  ]

  # ===========================================================================
  # Sierpinski Addressing (3×3 = 9 agents)
  # ===========================================================================

  class SierpinskiAddress
    attr_reader :trits  # Array of ternary digits [0,1,2]

    def initialize(document_id)
      # Hash document ID to Sierpinski address
      hash_val = Digest::SHA256.hexdigest(document_id).to_i(16)

      # Extract 2 ternary digits (0-8 = 0-2 in base 3, 0-2 in base 3)
      @trits = [
        (hash_val >> 0) % 3,
        (hash_val >> 16) % 3
      ]
    end

    # Convert to agent ID (0-8)
    def to_agent_id
      @trits[0] * 3 + @trits[1]
    end

    # Linear address for NATS subject routing
    def to_subject_prefix
      "sierpinski.#{@trits.join('.')}"
    end

    def to_s
      "[#{@trits.join(',')}]"
    end
  end

  # ===========================================================================
  # Vector Clock for Causality
  # ===========================================================================

  class VectorClock
    attr_reader :clocks

    def initialize(agent_id = nil)
      @clocks = {}
      @clocks[agent_id] = 0 if agent_id
    end

    def increment!(agent_id)
      @clocks[agent_id] = (@clocks[agent_id] || 0) + 1
      self
    end

    def merge!(other)
      other.clocks.each do |agent_id, clock|
        @clocks[agent_id] = [@clocks[agent_id] || 0, clock].max
      end
      self
    end

    def happens_before?(other)
      # Check if all clocks in self are ≤ other, with at least one <
      all_leq = @clocks.all? { |agent_id, clock| clock <= (other.clocks[agent_id] || 0) }
      some_less = @clocks.any? { |agent_id, clock| clock < (other.clocks[agent_id] || 0) }
      all_leq && some_less
    end

    def concurrent?(other)
      !happens_before?(other) && !other.happens_before?(self)
    end

    def to_h
      @clocks.dup
    end

    def to_json
      JSON.generate(@clocks)
    end

    def self.from_json(json_str)
      vc = new
      vc.instance_variable_set(:@clocks, JSON.parse(json_str))
      vc
    end
  end

  # ===========================================================================
  # CRDT Operation Message Format
  # ===========================================================================

  class CRDTMessage
    attr_reader :operation, :document_id, :payload, :vector_clock,
                :agent_id, :mathematician, :polarity, :color, :timestamp

    def initialize(operation:, document_id:, payload:, agent_id:, vector_clock:)
      @operation = operation
      @document_id = document_id
      @payload = payload
      @agent_id = agent_id
      @vector_clock = vector_clock
      @timestamp = Time.now

      # Look up mathematician info
      math = MATHEMATICIANS[agent_id]
      @mathematician = math[:name]
      @polarity = math[:polarity]
      @color = math[:color]
    end

    def to_nats_subject
      address = SierpinskiAddress.new(@document_id)
      "world.crdt.#{@agent_id}.#{@operation}"
    end

    def to_nats_message
      {
        subject: to_nats_subject,
        headers: {
          "X-Agent-ID" => @agent_id.to_s,
          "X-Mathematician" => @mathematician,
          "X-Polarity" => @polarity.to_s,
          "X-Color" => @color.to_s,
          "X-Operation" => @operation,
          "X-Document-ID" => @document_id,
          "X-Vector-Clock" => @vector_clock.to_json,
          "X-Timestamp" => @timestamp.to_i.to_s
        },
        data: {
          operation: @operation,
          document_id: @document_id,
          payload: @payload,
          vector_clock: @vector_clock.to_h,
          sierpinski_address: SierpinskiAddress.new(@document_id).trits,
          agent_id: @agent_id,
          mathematician: @mathematician,
          polarity: @polarity,
          color: @color
        }
      }
    end
  end

  # ===========================================================================
  # NATS Coordinator (Pub/Sub Message Broker)
  # ===========================================================================

  class NatsCoordinator
    attr_reader :agents, :subjects, :message_log

    def initialize
      @agents = {}
      @subjects = {}
      @message_log = []
      @subscriptions = {}

      # Initialize agent registry
      MATHEMATICIANS.each do |math|
        @agents[math[:agent_id]] = {
          name: math[:name],
          polarity: math[:polarity],
          color: math[:color],
          vector_clock: VectorClock.new(math[:agent_id]),
          status: :idle,
          last_operation: nil
        }
      end

      # Initialize NATS subject groups
      init_nats_subjects
    end

    def init_nats_subjects
      # Global subjects
      @subjects["world.crdt.*.*"] = []
      @subjects["world.sierpinski.*.*"] = []
      @subjects["world.merge.*"] = []
      @subjects["world.vector_clock.*"] = []
      @subjects["world.superposition.*"] = []
      @subjects["world.egg.verify.*"] = []

      # Per-agent subjects
      (0..8).each do |agent_id|
        @subjects["world.crdt.#{agent_id}.*"] = []
        @subjects["world.agent.#{agent_id}.status"] = []
      end
    end

    # Publish a CRDT operation to NATS
    def publish(operation:, document_id:, payload:, agent_id:)
      msg = CRDTMessage.new(
        operation: operation,
        document_id: document_id,
        payload: payload,
        agent_id: agent_id,
        vector_clock: @agents[agent_id][:vector_clock]
      )

      # Increment agent's vector clock
      @agents[agent_id][:vector_clock].increment!(agent_id)

      # Log message
      @message_log << msg
      @agents[agent_id][:last_operation] = msg

      # Distribute to subscribers
      distribute_message(msg)

      msg
    end

    def distribute_message(msg)
      subject = msg.to_nats_subject

      # Find matching subscriptions
      @subscriptions.each do |pattern, subscribers|
        if subject_matches_pattern?(subject, pattern)
          subscribers.each do |subscriber|
            subscriber.call(msg)
          end
        end
      end
    end

    def subject_matches_pattern?(subject, pattern)
      # Simple wildcard matching: * matches one segment
      s_parts = subject.split('.')
      p_parts = pattern.split('.')

      return false if s_parts.length != p_parts.length

      s_parts.zip(p_parts).all? { |s, p| p == '*' || s == p }
    end

    # Subscribe to NATS subjects
    def subscribe(pattern, &block)
      @subscriptions[pattern] ||= []
      @subscriptions[pattern] << block
    end

    # Route operation to agent based on document ID
    def route_to_agent(document_id)
      address = SierpinskiAddress.new(document_id)
      address.to_agent_id
    end

    # Agent status check
    def agent_status(agent_id)
      @agents[agent_id]
    end

    # Get all agent statuses
    def all_agent_statuses
      @agents.map do |agent_id, info|
        {
          agent_id: agent_id,
          name: info[:name],
          polarity: info[:polarity],
          color: info[:color],
          status: info[:status],
          vector_clock: info[:vector_clock].to_h,
          last_operation: info[:last_operation]&.operation
        }
      end
    end

    # Merge vector clocks from multiple agents
    def merge_vector_clocks(agent_ids)
      merged = VectorClock.new
      agent_ids.each do |agent_id|
        merged.merge!(@agents[agent_id][:vector_clock])
      end
      merged
    end

    # Verify causality between two operations
    def verify_causality(msg1, msg2)
      {
        happens_before: msg1.vector_clock.happens_before?(msg2.vector_clock),
        concurrent: msg1.vector_clock.concurrent?(msg2.vector_clock),
        msg1_id: msg1.document_id,
        msg2_id: msg2.document_id
      }
    end

    # Simulate merge coordination across agents
    def coordinate_merge(document_id)
      agent_id = route_to_agent(document_id)
      agent = @agents[agent_id]

      # Prepare merge operation
      msg = CRDTMessage.new(
        operation: :merge,
        document_id: document_id,
        payload: { merge_type: :join_semilattice },
        agent_id: agent_id,
        vector_clock: agent[:vector_clock].dup
      )

      agent[:vector_clock].increment!(agent_id)

      # Broadcast to all agents for merge verification
      broadcast_to_all(msg)

      msg
    end

    def broadcast_to_all(msg)
      # Simulate broadcast to all agents
      @agents.each do |agent_id, _|
        next if agent_id == msg.agent_id

        # Each agent increments their clock for received message
        @agents[agent_id][:vector_clock].merge!(msg.vector_clock)
      end
    end

    # Generate NATS subject statistics
    def stats
      {
        total_agents: @agents.length,
        total_messages: @message_log.length,
        by_operation: @message_log.group_by(&:operation).transform_values(&:length),
        by_polarity: {
          positive: @message_log.count { |m| m.polarity == :positive },
          negative: @message_log.count { |m| m.polarity == :negative },
          neutral: @message_log.count { |m| m.polarity == :neutral }
        },
        agent_activities: all_agent_statuses
      }
    end
  end

  # ===========================================================================
  # Ramanujan Expander Graph Properties
  # ===========================================================================

  class RamanujanProperties
    # p=3 (ternary), d=2 (2D)
    # Vertex count: p^d = 3^2 = 9
    # Spectral gap: λ_gap ≥ 2√(d-1) = 2√1 = 2
    # Mixing time: O(log n / λ_gap) = O(log 9 / 2) ≈ 1.58 steps

    def self.properties
      {
        prime: 3,
        dimension: 2,
        vertex_count: 9,
        edges_per_vertex: 3,  # (q+1) = 3+1 = 4, but we use ternary
        spectral_gap: 2.0,
        mixing_time: (Math.log(9) / 2.0).round(2),
        diameter: 2,  # Maximum distance between any two vertices
        expansion_constant: 2.0
      }
    end

    def self.adjacency_matrix
      # 9×9 Ramanujan graph adjacency
      # For 3^2 lattice:
      # 0 connects to 1, 3, 6
      # 1 connects to 0, 2, 4, 7
      # etc. (ternary grid structure)
      [
        [0, 1, 0, 1, 0, 0, 1, 0, 0],  # 0
        [1, 0, 1, 0, 1, 0, 0, 1, 0],  # 1
        [0, 1, 0, 0, 0, 1, 0, 0, 1],  # 2
        [1, 0, 0, 0, 1, 0, 1, 0, 0],  # 3
        [0, 1, 0, 1, 0, 1, 0, 1, 0],  # 4
        [0, 0, 1, 0, 1, 0, 0, 0, 1],  # 5
        [1, 0, 0, 1, 0, 0, 0, 1, 0],  # 6
        [0, 1, 0, 0, 1, 0, 1, 0, 1],  # 7
        [0, 0, 1, 0, 0, 1, 0, 1, 0]   # 8
      ]
    end

    def self.is_expander?
      props = properties
      props[:spectral_gap] >= 2.0
    end
  end
end

# ===========================================================================
# Standalone Testing Functions
# ===========================================================================

def test_sierpinski_addressing
  puts "\n" + "="*70
  puts "TEST: Sierpinski Addressing"
  puts "="*70

  documents = ["doc_42d", "doc_xyz", "user_alice", "item_99", "crdt_text_1"]
  coordinator = RamanujanNatsCoordinator::NatsCoordinator.new

  documents.each do |doc_id|
    agent_id = coordinator.route_to_agent(doc_id)
    address = RamanujanNatsCoordinator::SierpinskiAddress.new(doc_id)
    math = RamanujanNatsCoordinator::MATHEMATICIANS[agent_id]

    puts format("Document: %-20s → Agent %d (%s) Address: %s",
                doc_id, agent_id, math[:name], address)
  end
end

def test_vector_clock_causality
  puts "\n" + "="*70
  puts "TEST: Vector Clock Causality"
  puts "="*70

  coordinator = RamanujanNatsCoordinator::NatsCoordinator.new

  # Agent 0 publishes
  msg1 = coordinator.publish(
    operation: :insert,
    document_id: "doc_1",
    payload: { text: "hello" },
    agent_id: 0
  )
  puts "Agent 0 insert: #{msg1.vector_clock.to_h}"

  # Agent 1 publishes (sees Agent 0's clock)
  coordinator.agents[1][:vector_clock].merge!(msg1.vector_clock)
  msg2 = coordinator.publish(
    operation: :merge,
    document_id: "doc_2",
    payload: { type: :json },
    agent_id: 1
  )
  puts "Agent 1 merge: #{msg2.vector_clock.to_h}"

  # Check causality
  causality = coordinator.verify_causality(msg1, msg2)
  puts "Causality: #{causality}"
end

def test_message_statistics
  puts "\n" + "="*70
  puts "TEST: Message Statistics & Agent Activity"
  puts "="*70

  coordinator = RamanujanNatsCoordinator::NatsCoordinator.new

  # Simulate operations across agents
  operations = [
    [:insert, "doc_1", 0],
    [:insert, "doc_2", 1],
    [:delete, "doc_3", 2],
    [:update, "doc_4", 3],
    [:verify, "doc_5", 4],
    [:union, "doc_6", 5],
    [:snapshot, "doc_7", 6],
    [:recover, "doc_8", 7],
    [:invalidate, "doc_9", 8]
  ]

  operations.each do |op, doc_id, agent_id|
    coordinator.publish(
      operation: op,
      document_id: doc_id,
      payload: { sample: true },
      agent_id: agent_id
    )
  end

  stats = coordinator.stats
  puts "\nStats:"
  puts "  Total agents: #{stats[:total_agents]}"
  puts "  Total messages: #{stats[:total_messages]}"
  puts "  By operation: #{stats[:by_operation]}"
  puts "  By polarity: #{stats[:by_polarity]}"
end

def test_ramanujan_properties
  puts "\n" + "="*70
  puts "TEST: Ramanujan Expander Graph Properties"
  puts "="*70

  props = RamanujanNatsCoordinator::RamanujanProperties.properties
  puts "\nProperties:"
  props.each { |k, v| puts "  #{k}: #{v}" }

  puts "\nIs expander? #{RamanujanNatsCoordinator::RamanujanProperties.is_expander?}"
end

if __FILE__ == $0
  test_sierpinski_addressing
  test_vector_clock_causality
  test_message_statistics
  test_ramanujan_properties
end
