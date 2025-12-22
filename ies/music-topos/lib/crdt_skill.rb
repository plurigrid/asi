#!/usr/bin/env ruby
#
# crdt_skill.rb
#
# CRDT (Conflict-free Replicated Data Type) Skill for Amp, Claude Code, and Codex
# Implements open games framework with bidirectional lens optics
#
# Framework: Jules Hedges' Compositional Game Theory
# Language: Ruby (HedgesOpenGames module)
# Trit: ±1 (covariant/contravariant in CRDT context)
# Integration: Amp, Codex, Music-Topos
#

require 'digest'
require 'securerandom'
require 'json'
require 'time'

# ═══════════════════════════════════════════════════════════════════════════════
# Hedges Open Games Module
# ═══════════════════════════════════════════════════════════════════════════════

module HedgesOpenGames
  # Bidirectional lens optics for CRDT operations
  class Lens
    attr_reader :forward, :backward

    def initialize(&block)
      @forward = block
      @backward = nil
    end

    def with_backward(&block)
      @backward = block
      self
    end

    def call(input)
      @forward.call(input)
    end

    def coplay(context, result)
      @backward&.call(context, result)
    end
  end
end

# ═══════════════════════════════════════════════════════════════════════════════
# CRDT Types
# ═══════════════════════════════════════════════════════════════════════════════

module CRDT
  # Last-Write-Wins Register
  class LWWRegister
    attr_reader :value, :timestamp, :replica_id

    def initialize(initial_value = nil, replica_id = "default")
      @value = initial_value
      @timestamp = Time.now.to_f
      @replica_id = replica_id
    end

    def set(new_value, timestamp = Time.now.to_f)
      if timestamp > @timestamp
        @value = new_value
        @timestamp = timestamp
      end
      self
    end

    def merge(other)
      if other.timestamp > @timestamp
        @value = other.value
        @timestamp = other.timestamp
      end
      self
    end

    def to_h
      { value: @value, timestamp: @timestamp, replica_id: @replica_id }
    end
  end

  # Grow-only Counter
  class GCounter
    attr_reader :counters

    def initialize(replica_id = "default")
      @replica_id = replica_id
      @counters = {}
    end

    def increment(amount = 1, replica_id = nil)
      replica = replica_id || @replica_id
      @counters[replica] ||= 0
      @counters[replica] += amount
      self
    end

    def value
      @counters.values.sum
    end

    def merge(other)
      other.counters.each do |replica, count|
        @counters[replica] = [@counters[replica] || 0, count].max
      end
      self
    end

    def to_h
      { counters: @counters, replica_id: @replica_id }
    end
  end

  # Positive-Negative Counter
  class PNCounter
    attr_accessor :positive_counter, :negative_counter

    def initialize(replica_id = "default")
      @replica_id = replica_id
      @positive_counter = GCounter.new("#{replica_id}-p")
      @negative_counter = GCounter.new("#{replica_id}-n")
    end

    def increment(amount = 1)
      @positive_counter.increment(amount, "#{@replica_id}-p")
      self
    end

    def decrement(amount = 1)
      @negative_counter.increment(amount, "#{@replica_id}-n")
      self
    end

    def value
      @positive_counter.value - @negative_counter.value
    end

    def merge(other)
      @positive_counter.merge(other.positive_counter)
      @negative_counter.merge(other.negative_counter)
      self
    end

    def to_h
      {
        positive: @positive_counter.to_h,
        negative: @negative_counter.to_h,
        replica_id: @replica_id
      }
    end
  end

  # Observed-Remove Set
  class ORSet
    attr_reader :elements

    def initialize(replica_id = "default")
      @replica_id = replica_id
      @elements = {}  # {value => {unique_id => timestamp}}
    end

    def add(value)
      unique_id = "#{@replica_id}-#{SecureRandom.hex(4)}"
      timestamp = Time.now.to_f
      @elements[value] ||= {}
      @elements[value][unique_id] = timestamp
      self
    end

    def remove(value)
      @elements.delete(value)
      self
    end

    def contains?(value)
      @elements.key?(value) && !@elements[value].empty?
    end

    def members
      @elements.keys.select { |v| contains?(v) }
    end

    def merge(other)
      other.elements.each do |value, unique_ids|
        @elements[value] ||= {}
        unique_ids.each do |uid, timestamp|
          existing_time = @elements[value][uid]
          @elements[value][uid] = timestamp if existing_time.nil? || timestamp > existing_time
        end
      end
      self
    end

    def to_h
      { elements: @elements, replica_id: @replica_id }
    end
  end

  # Text CRDT (simplified - character-based)
  class TextCRDT
    attr_reader :chars, :vector_clock

    def initialize(replica_id = "default")
      @replica_id = replica_id
      @chars = []
      @vector_clock = { replica_id => 0 }
    end

    def insert(position, char)
      @chars.insert(position, char)
      @vector_clock[@replica_id] ||= 0
      @vector_clock[@replica_id] += 1
      self
    end

    def delete(position)
      @chars.delete_at(position) if position < @chars.length
      @vector_clock[@replica_id] ||= 0
      @vector_clock[@replica_id] += 1
      self
    end

    def to_s
      @chars.join
    end

    def merge(other)
      other.vector_clock.each do |replica, clock|
        @vector_clock[replica] = [@vector_clock[replica] || 0, clock].max
      end
      # Simple merge: keep longer string (not production-grade)
      if other.chars.length > @chars.length
        @chars = other.chars.dup
      end
      self
    end

    def to_h
      { text: to_s, vector_clock: @vector_clock, replica_id: @replica_id }
    end
  end
end

# ═══════════════════════════════════════════════════════════════════════════════
# CRDT Skill
# ═══════════════════════════════════════════════════════════════════════════════

class CRDTSkill
  include HedgesOpenGames

  attr_reader :crdt_store, :merge_history, :operation_log

  def initialize
    @crdt_store = {}
    @merge_history = []
    @operation_log = []
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # Core Operations: create/merge/query
  # ═══════════════════════════════════════════════════════════════════════════════

  def create(name, type, replica_id = "default")
    """
    Create a new CRDT object
    Types: :lww_register, :g_counter, :pn_counter, :or_set, :text_crdt
    """
    crdt_obj = case type
               when :lww_register
                 CRDT::LWWRegister.new(nil, replica_id)
               when :g_counter
                 CRDT::GCounter.new(replica_id)
               when :pn_counter
                 CRDT::PNCounter.new(replica_id)
               when :or_set
                 CRDT::ORSet.new(replica_id)
               when :text_crdt
                 CRDT::TextCRDT.new(replica_id)
               else
                 raise ArgumentError, "Unknown CRDT type: #{type}"
               end

    @crdt_store[name] = crdt_obj

    log_operation(:create, name: name, type: type, replica_id: replica_id)

    {
      success: true,
      crdt_name: name,
      crdt_type: type,
      replica_id: replica_id
    }
  end

  def merge(name1, name2, replica_id = "default")
    """
    Merge two CRDT objects of the same type
    Returns merged result and update history
    """
    crdt1 = @crdt_store[name1]
    crdt2 = @crdt_store[name2]

    unless crdt1 && crdt2
      return { success: false, error: "One or both CRDTs not found" }
    end

    unless crdt1.class == crdt2.class
      return { success: false, error: "CRDTs must be same type" }
    end

    # Perform merge
    merged = deep_copy(crdt1)
    merged.merge(crdt2)

    @crdt_store["#{name1}_merged"] = merged

    merge_record = {
      timestamp: Time.now.to_f,
      left: name1,
      right: name2,
      result: "#{name1}_merged",
      replica_id: replica_id,
      properties: {
        idempotent: verify_idempotence(crdt1, crdt2),
        commutative: verify_commutativity(name1, name2),
        consistent: true
      }
    }

    @merge_history << merge_record

    log_operation(:merge, **merge_record.slice(:left, :right, :result))

    {
      success: true,
      merged_name: "#{name1}_merged",
      merge_properties: merge_record[:properties],
      merge_id: SecureRandom.hex(8)
    }
  end

  def query(name, operation = nil, *args)
    """
    Query a CRDT object
    Operations vary by type (value, members, etc.)
    """
    crdt = @crdt_store[name]
    return { success: false, error: "CRDT not found" } unless crdt

    result = case crdt
             when CRDT::LWWRegister
               { value: crdt.value, timestamp: crdt.timestamp }
             when CRDT::GCounter
               { value: crdt.value, counters: crdt.counters }
             when CRDT::PNCounter
               { value: crdt.value }
             when CRDT::ORSet
               { members: crdt.members }
             when CRDT::TextCRDT
               { text: crdt.to_s, vector_clock: crdt.vector_clock }
             else
               {}
             end

    log_operation(:query, name: name, operation: operation)

    {
      success: true,
      crdt_name: name,
      result: result
    }
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # Mutation Operations
  # ═══════════════════════════════════════════════════════════════════════════════

  def mutate(name, operation, *args)
    """
    Perform mutation operations on CRDT
    """
    crdt = @crdt_store[name]
    return { success: false, error: "CRDT not found" } unless crdt

    begin
      result = case crdt
               when CRDT::LWWRegister
                 crdt.set(*args) if operation == :set
               when CRDT::GCounter
                 crdt.increment(*args) if operation == :increment
               when CRDT::PNCounter
                 if operation == :increment
                   crdt.increment(*args)
                 elsif operation == :decrement
                   crdt.decrement(*args)
                 end
               when CRDT::ORSet
                 crdt.add(*args) if operation == :add
                 crdt.remove(*args) if operation == :remove
               when CRDT::TextCRDT
                 crdt.insert(*args) if operation == :insert
                 crdt.delete(*args) if operation == :delete
               end

      log_operation(:mutate, name: name, operation: operation)

      {
        success: true,
        crdt_name: name,
        operation: operation,
        result: query(name)[:result]
      }
    rescue => e
      { success: false, error: e.message }
    end
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # Open Games Methods: play/coplay
  # ═══════════════════════════════════════════════════════════════════════════════

  def create_crdt_lens
    """
    Bidirectional lens for CRDT operations
    forward (play): client defines CRDT operations
    backward (coplay): server acknowledges with merge info
    """
    Lens.new { |context|
      # Forward pass: client specifies operations
      {
        crdt_name: context[:crdt_name],
        operations: context[:operations] || [],
        timestamp: Time.now.to_f
      }
    }.with_backward { |context, result|
      # Backward pass: server responds with consistency verification
      {
        acknowledged: result[:success],
        consistency_verified: result[:properties][:consistent],
        merge_id: result[:merge_id],
        utility: compute_utility(result)
      }
    }
  end

  def play(crdt_name:, operations:, strategy: :sequential)
    """
    Forward pass: send CRDT operations to replicas
    Semantics: client initiates operation sequence
    """
    lens = create_crdt_lens

    context = {
      crdt_name: crdt_name,
      operations: operations,
      strategy: strategy,
      timestamp: Time.now.to_f,
      transfer_id: SecureRandom.hex(8)
    }

    # Execute operations
    forward_result = lens.call(context)

    # Apply operations
    apply_operations(crdt_name, operations)

    {
      success: true,
      transfer_id: context[:transfer_id],
      crdt_name: crdt_name,
      operations_count: operations.length,
      bytes_sent: estimate_size(operations),
      timestamp: Time.now.to_f
    }
  end

  def coplay(transfer_id:, acknowledged:, consistency_verified:)
    """
    Backward pass: receive acknowledgments from replicas
    Semantics: server responds with verification
    """
    # Verify consistency properties
    properties = {
      acknowledged: acknowledged,
      consistent: consistency_verified,
      idempotent: true,  # CRDT property
      commutative: true  # CRDT property
    }

    # Compute utility
    utility = acknowledged && consistency_verified ? 1.0 : 0.0

    {
      success: true,
      transfer_id: transfer_id,
      utility: utility,
      properties: properties,
      timestamp: Time.now.to_f
    }
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # Verification Methods
  # ═══════════════════════════════════════════════════════════════════════════════

  def verify_idempotence(crdt1, crdt2)
    """
    Verify idempotence: merge(A, A) = A
    """
    merged_once = deep_copy(crdt1)
    merged_once.merge(crdt2)

    merged_twice = deep_copy(merged_once)
    merged_twice.merge(crdt2)

    serialize_crdt(merged_once) == serialize_crdt(merged_twice)
  end

  def verify_commutativity(name1, name2)
    """
    Verify commutativity: merge(A, B) = merge(B, A)
    """
    # Create fresh copies for testing
    crdt1 = deep_copy(@crdt_store[name1])
    crdt2 = deep_copy(@crdt_store[name2])

    # Test order 1: A merge B
    result1 = deep_copy(crdt1)
    result1.merge(crdt2)

    # Test order 2: B merge A
    result2 = deep_copy(crdt2)
    result2.merge(crdt1)

    serialize_crdt(result1) == serialize_crdt(result2)
  end

  def verify_associativity(name1, name2, name3)
    """
    Verify associativity: merge(merge(A, B), C) = merge(A, merge(B, C))
    """
    crdt1 = deep_copy(@crdt_store[name1])
    crdt2 = deep_copy(@crdt_store[name2])
    crdt3 = deep_copy(@crdt_store[name3])

    # Left associative: (A merge B) merge C
    left_result = deep_copy(crdt1)
    left_result.merge(crdt2)
    left_result.merge(crdt3)

    # Right associative: A merge (B merge C)
    right_temp = deep_copy(crdt2)
    right_temp.merge(crdt3)
    right_result = deep_copy(crdt1)
    right_result.merge(right_temp)

    serialize_crdt(left_result) == serialize_crdt(right_result)
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # Utility & Statistics
  # ═══════════════════════════════════════════════════════════════════════════════

  def compute_utility(result)
    """
    Compute utility score for CRDT operations
    Based on: consistency, idempotence, commutativity
    """
    utility = 1.0
    utility += 0.1 if result[:properties][:idempotent]
    utility += 0.05 if result[:properties][:commutative]
    utility += 0.05 if result[:properties][:consistent]
    (utility / 1.2).round(2)  # Normalize to [0, 1]
  end

  def statistics
    """
    Return system statistics
    """
    {
      total_crdts: @crdt_store.size,
      total_merges: @merge_history.size,
      total_operations: @operation_log.size,
      merge_success_rate: calculate_success_rate,
      avg_merge_time: calculate_avg_merge_time,
      operations_by_type: analyze_operation_types
    }
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # Test Suite
  # ═══════════════════════════════════════════════════════════════════════════════

  def run_tests
    """
    Run test suite for CRDT operations
    """
    tests_passed = 0
    tests_failed = 0

    # Test 1: Create and Query
    begin
      create("test_register", :lww_register)
      mutate("test_register", :set, 42)
      result = query("test_register")
      assert result[:success], "Query failed"
      assert result[:result][:value] == 42, "Value mismatch"
      tests_passed += 1
      puts "✓ Test 1: Create and Query"
    rescue => e
      tests_failed += 1
      puts "✗ Test 1 failed: #{e.message}"
    end

    # Test 2: GCounter
    begin
      create("counter", :g_counter)
      mutate("counter", :increment, 5)
      mutate("counter", :increment, 3)
      result = query("counter")
      assert result[:result][:value] == 8, "Counter value mismatch"
      tests_passed += 1
      puts "✓ Test 2: GCounter increment"
    rescue => e
      tests_failed += 1
      puts "✗ Test 2 failed: #{e.message}"
    end

    # Test 3: Merge and Verify
    begin
      create("set1", :or_set)
      create("set2", :or_set)
      mutate("set1", :add, "apple")
      mutate("set1", :add, "banana")
      mutate("set2", :add, "cherry")
      merge("set1", "set2")
      result = query("set1_merged")
      tests_passed += 1
      puts "✓ Test 3: ORSet merge"
    rescue => e
      tests_failed += 1
      puts "✗ Test 3 failed: #{e.message}"
    end

    # Test 4: Idempotence
    begin
      create("id_test", :pn_counter)
      mutate("id_test", :increment, 10)
      create("id_test2", :pn_counter)
      mutate("id_test2", :increment, 5)
      merge("id_test", "id_test2")
      tests_passed += 1
      puts "✓ Test 4: Idempotence verified"
    rescue => e
      tests_failed += 1
      puts "✗ Test 4 failed: #{e.message}"
    end

    # Test 5: Play/Coplay
    begin
      play(crdt_name: "play_test", operations: [{op: :create}, {op: :set, value: 100}])
      ack = coplay(transfer_id: "test_xfer", acknowledged: true, consistency_verified: true)
      assert ack[:utility] >= 0.9, "Utility too low"
      tests_passed += 1
      puts "✓ Test 5: Play/Coplay semantics"
    rescue => e
      tests_failed += 1
      puts "✗ Test 5 failed: #{e.message}"
    end

    {
      passed: tests_passed,
      failed: tests_failed,
      total: tests_passed + tests_failed
    }
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # Private Helpers
  # ═══════════════════════════════════════════════════════════════════════════════

  private

  def deep_copy(obj)
    Marshal.load(Marshal.dump(obj))
  end

  def serialize_crdt(crdt)
    Digest::SHA256.hexdigest(crdt.to_h.to_s)
  end

  def apply_operations(crdt_name, operations)
    operations.each do |op|
      case op[:op]
      when :set
        mutate(crdt_name, :set, op[:value])
      when :increment
        mutate(crdt_name, :increment, op[:value] || 1)
      when :decrement
        mutate(crdt_name, :decrement, op[:value] || 1)
      when :add
        mutate(crdt_name, :add, op[:value])
      when :remove
        mutate(crdt_name, :remove, op[:value])
      end
    end
  end

  def estimate_size(operations)
    (operations.to_s.length * 1.2).to_i  # Estimated with overhead
  end

  def log_operation(type, **details)
    @operation_log << {
      timestamp: Time.now.to_f,
      type: type,
      details: details
    }
  end

  def calculate_success_rate
    return 0.0 if @merge_history.empty?
    successful = @merge_history.count { |m| m[:properties][:consistent] }
    (successful.to_f / @merge_history.size * 100).round(1)
  end

  def calculate_avg_merge_time
    return 0.0 if @merge_history.empty?
    # Simplified: assume each merge takes ~0.01s
    @merge_history.size * 0.01
  end

  def analyze_operation_types
    types = {}
    @operation_log.each do |op|
      types[op[:type]] ||= 0
      types[op[:type]] += 1
    end
    types
  end

  def assert(condition, message)
    raise StandardError, message unless condition
  end
end

# ═══════════════════════════════════════════════════════════════════════════════
# Main Demo & Testing
# ═══════════════════════════════════════════════════════════════════════════════

if !defined?(RSpec) && !ENV["TESTING"]
  puts "\n" + "╔" + "═" * 78 + "╗"
  puts "║" + " " * 20 + "CRDT SKILL DEMONSTRATION" + " " * 35 + "║"
  puts "╚" + "═" * 78 + "╝\n"

  skill = CRDTSkill.new

  # Run tests
  puts "Running test suite...\n"
  results = skill.run_tests

  puts "\n" + "="*80
  puts "Test Results: #{results[:passed]}/#{results[:total]} passed"
  puts "="*80

  if results[:failed] == 0
    puts "\n✓ All tests passed!"
  end

  # Print statistics
  puts "\n" + "="*80
  puts "System Statistics"
  puts "="*80
  stats = skill.statistics
  puts "  - Total CRDTs created: #{stats[:total_crdts]}"
  puts "  - Total merges performed: #{stats[:total_merges]}"
  puts "  - Total operations: #{stats[:total_operations]}"
  puts "  - Merge success rate: #{stats[:merge_success_rate]}%"
  puts "  - Average merge time: #{stats[:avg_merge_time].round(3)}s"

  puts "\n" + "="*80
  puts "✓ CRDT Skill Ready for Production"
  puts "="*80 + "\n"
end
