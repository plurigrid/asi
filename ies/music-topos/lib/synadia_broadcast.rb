# lib/synadia_broadcast.rb
#
# SYNADIA BROADCAST: NATS/JetStream Integration for WORLD Broadcast System
#
# Extends WorldBroadcast with distributed messaging via Synadia/NATS:
# - Pub/Sub for real-time mathematician broadcasts
# - JetStream for durable s-expression streams
# - Subject hierarchy: world.{mathematician}.{operation}.{address}
# - String diagram counterfactual rewriting via message headers
# - CRDT.el compatible message format
#
# Architecture (Open Games as NATS subjects):
#   World Action (covariant):   world.forward.{mathematician} → publishes
#   Coworld Action (contravariant): world.backward.{mathematician} → subscribes to utility
#
# Usage:
#   just synadia-broadcast         # Start NATS-connected broadcast
#   just synadia-logicians         # de Paiva ⊗ Hedges ⊗ Girard over NATS
#
# Requires: nats-server running (brew install nats-server && nats-server)

require_relative 'world_broadcast'
require 'json'
require 'securerandom'

# NATS client is optional - demo mode works without it
NATS_AVAILABLE = begin
  require 'nats/client'
  true
rescue LoadError
  false
end

module SynadiaBroadcast
  # ═══════════════════════════════════════════════════════════════
  # NATS SUBJECT HIERARCHY (String Diagram Structure)
  # ═══════════════════════════════════════════════════════════════
  #
  # Subjects form a string diagram where:
  # - Horizontal composition: mathematician₁.op ⊗ mathematician₂.op
  # - Vertical composition: forward.* ; backward.* (sequential)
  #
  # Subject patterns:
  #   world.broadcast.{mathematician}     - Main broadcast channel
  #   world.forward.{mathematician}       - World action (covariant)
  #   world.backward.{mathematician}      - Coworld action (contravariant)
  #   world.superposition.{epoch}         - Combined tripartite state
  #   world.sierpinski.{address}          - Gasket-indexed s-expressions
  #   world.zeta.{mathematician}          - Analytic continuation results
  #   world.crdt.{operation}              - CRDT operations for crdt.el
  
  SUBJECT_PREFIX = "world"
  
  # JetStream stream configuration
  STREAM_CONFIG = {
    name: "WORLD_BROADCAST",
    subjects: ["world.>"],  # Capture all world.* subjects
    retention: :limits,
    max_msgs: 10_000,
    max_bytes: 100 * 1024 * 1024,  # 100MB
    max_age: 24 * 60 * 60 * 1_000_000_000,  # 24 hours in nanoseconds
    storage: :file,
    discard: :old,
    duplicate_window: 120 * 1_000_000_000  # 2 minutes
  }
  
  # ═══════════════════════════════════════════════════════════════
  # STRING DIAGRAM HEADERS (Counterfactual Rewriting Metadata)
  # ═══════════════════════════════════════════════════════════════
  #
  # Headers enable counterfactual reasoning:
  # - X-Polarity: positive/negative/neutral (Girard)
  # - X-Counterfactual-Branch: which alternate history
  # - X-Sierpinski-Depth: fractal depth for conjugacy
  # - X-Zeta-Regularized: analytic continuation value
  # - X-Open-Game-Port: input/output/utility/strategy
  
  module Headers
    def self.build(mathematician:, operation:, address:, polarity:, epoch:, **extra)
      {
        "X-Mathematician" => mathematician.to_s,
        "X-Operation" => operation.to_s,
        "X-Sierpinski-Address" => address.join,
        "X-Sierpinski-Depth" => address.size.to_s,
        "X-Polarity" => polarity.to_s,
        "X-Epoch" => epoch.to_s,
        "X-Timestamp" => Time.now.to_f.to_s,
        "X-Counterfactual-Branch" => SecureRandom.uuid[0..7],
        "X-Message-ID" => SecureRandom.uuid
      }.merge(extra.transform_keys { |k| "X-#{k.to_s.gsub('_', '-').split('-').map(&:capitalize).join('-')}" })
    end
    
    def self.parse(headers)
      return {} unless headers
      headers.transform_keys { |k| k.sub(/^X-/, '').downcase.gsub('-', '_').to_sym }
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # NATS MESSAGE ENVELOPE (CRDT.el Compatible)
  # ═══════════════════════════════════════════════════════════════
  
  class MessageEnvelope
    attr_reader :subject, :data, :headers, :reply
    
    def initialize(subject:, data:, headers: {}, reply: nil)
      @subject = subject
      @data = data
      @headers = headers
      @reply = reply
    end
    
    def to_nats_msg
      {
        subject: @subject,
        data: @data.is_a?(String) ? @data : JSON.generate(@data),
        header: @headers,
        reply: @reply
      }
    end
    
    def self.from_nats_msg(msg)
      new(
        subject: msg.subject,
        data: begin JSON.parse(msg.data, symbolize_names: true) rescue msg.data end,
        headers: msg.header || {},
        reply: msg.reply
      )
    end
    
    # Convert to s-expression string (CRDT.el format)
    def to_sexp
      sexp_data = @data.is_a?(Hash) ? @data : { value: @data }
      WorldBroadcast::SexpGenerator.to_string([
        @subject.split('.').last.to_sym,
        sexp_data,
        :meta, Headers.parse(@headers)
      ])
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # SYNADIA BROADCASTER: NATS-Connected Open Game Agent
  # ═══════════════════════════════════════════════════════════════
  
  class SynadiaBroadcaster
    attr_reader :nats, :js, :mathematician_key, :profile, :agent
    
    def initialize(mathematician_key, nats_url: "nats://127.0.0.1:4222")
      @mathematician_key = mathematician_key
      @profile = WorldBroadcast::MATHEMATICIAN_PROFILES[mathematician_key]
      raise ArgumentError, "Unknown mathematician: #{mathematician_key}" unless @profile
      
      @agent = WorldBroadcast::MathematicianAgent.new(mathematician_key)
      @nats_url = nats_url
      @nats = nil
      @js = nil
      @subscriptions = []
    end
    
    def connect!
      @nats = NATS.connect(@nats_url)
      
      # Setup JetStream if available
      begin
        @js = @nats.jetstream
        ensure_stream!
      rescue => e
        puts "  JetStream not available: #{e.message} (using core NATS)"
        @js = nil
      end
      
      self
    end
    
    def ensure_stream!
      return unless @js
      
      begin
        @js.stream_info(STREAM_CONFIG[:name])
      rescue
        @js.add_stream(**STREAM_CONFIG)
      end
    end
    
    def disconnect!
      @subscriptions.each { |sub| sub.unsubscribe rescue nil }
      @nats&.close
    end
    
    # ═════════════════════════════════════════════════════════════
    # WORLD ACTION: Publish (Covariant, Forward)
    # ═════════════════════════════════════════════════════════════
    
    def broadcast_step!(epoch)
      result = @agent.step!
      
      # Build message
      headers = Headers.build(
        mathematician: @profile[:name],
        operation: result[:operation],
        address: result[:address],
        polarity: @profile[:polarity],
        epoch: epoch,
        world_action: @profile[:world_action]&.forward_fn,
        coworld_action: @profile[:coworld_action]&.backward_fn,
        zeta_preference: @profile[:zeta_preference]
      )
      
      color_value = begin
        result[:sexp].last[:color]
      rescue
        nil
      end
      
      payload = {
        epoch: epoch,
        mathematician: @mathematician_key,
        name: @profile[:name],
        operation: result[:operation],
        args: result[:args],
        address: result[:address],
        conjugacy_class: result[:conjugacy_class],
        equivalence_class: result[:equivalence_class],
        sexp: WorldBroadcast::SexpGenerator.to_string(result[:sexp]),
        color: color_value
      }
      
      # Publish to multiple subjects (string diagram decomposition)
      subjects = [
        "#{SUBJECT_PREFIX}.broadcast.#{@mathematician_key}",
        "#{SUBJECT_PREFIX}.forward.#{@mathematician_key}",
        "#{SUBJECT_PREFIX}.sierpinski.#{result[:address].join}",
        "#{SUBJECT_PREFIX}.operation.#{result[:operation]}"
      ]
      
      subjects.each do |subject|
        publish(subject, payload, headers)
      end
      
      { result: result, subjects: subjects, payload: payload }
    end
    
    def publish(subject, data, headers = {})
      msg_data = data.is_a?(String) ? data : JSON.generate(data)
      
      if @js
        @js.publish(subject, msg_data, header: headers)
      else
        @nats.publish(subject, msg_data, header: headers)
      end
    end
    
    # ═════════════════════════════════════════════════════════════
    # COWORLD ACTION: Subscribe (Contravariant, Backward)
    # ═════════════════════════════════════════════════════════════
    
    def subscribe_backward!(pattern = "#{SUBJECT_PREFIX}.backward.#{@mathematician_key}", &block)
      sub = @nats.subscribe(pattern) do |msg|
        envelope = MessageEnvelope.from_nats_msg(msg)
        
        # Execute coworld action with received utility
        utility = envelope.data[:utility] || envelope.data
        backward_result = @agent.coworld_action(utility)
        
        # Reply if request pattern
        if msg.reply
          reply_data = {
            mathematician: @mathematician_key,
            strategy: backward_result[:strategy],
            fn: backward_result[:fn]
          }
          @nats.publish(msg.reply, JSON.generate(reply_data))
        end
        
        block&.call(envelope, backward_result)
      end
      
      @subscriptions << sub
      sub
    end
    
    # Subscribe to superposition channel (tripartite combined state)
    def subscribe_superposition!(&block)
      sub = @nats.subscribe("#{SUBJECT_PREFIX}.superposition.*") do |msg|
        envelope = MessageEnvelope.from_nats_msg(msg)
        block&.call(envelope)
      end
      
      @subscriptions << sub
      sub
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # TRIPARTITE SYNADIA SYSTEM: 3 Broadcasters in Superposition
  # ═══════════════════════════════════════════════════════════════
  
  class TripartiteSynadiaSystem
    attr_reader :broadcasters, :epoch, :nats_url
    
    def initialize(mathematician_keys = [:ramanujan, :grothendieck, :euler], nats_url: "nats://127.0.0.1:4222")
      @mathematician_keys = mathematician_keys
      @nats_url = nats_url
      @broadcasters = []
      @epoch = 0
      @coordinator_nats = nil
    end
    
    def connect!
      # Create broadcaster for each mathematician
      @broadcasters = @mathematician_keys.map do |key|
        SynadiaBroadcaster.new(key, nats_url: @nats_url).tap(&:connect!)
      end
      
      # Coordinator connection for superposition publishing
      @coordinator_nats = NATS.connect(@nats_url)
      
      self
    end
    
    def disconnect!
      @broadcasters.each(&:disconnect!)
      @coordinator_nats&.close
    end
    
    def step!
      @epoch += 1
      
      # All mathematicians broadcast in parallel (conceptually)
      results = @broadcasters.map { |b| b.broadcast_step!(@epoch) }
      
      # Compute and publish superposition
      superposition = compute_superposition(results.map { |r| r[:result] })
      
      publish_superposition!(superposition)
      
      { epoch: @epoch, results: results, superposition: superposition }
    end
    
    def compute_superposition(results)
      weights = @broadcasters.map { |b| polarity_weight(b.profile[:polarity]) }
      weight_sum = weights.map(&:abs).sum
      weight_sum = 1.0 if weight_sum.zero?
      
      # Combine Sierpinski addresses
      first_address = results.first[:address] || []
      combined = first_address.each_with_index.map do |_, i|
        votes = results.map.with_index { |r, j| (r[:address][i] || 0).to_i * weights[j] }
        ((votes.sum / weight_sum) + 1).round % 3
      end
      
      {
        epoch: @epoch,
        addresses: results.map { |r| r[:address] },
        combined: combined,
        conjugacy: WorldBroadcast::SierpinskiAddress.conjugacy_class(combined),
        mathematicians: @mathematician_keys,
        polarities: @broadcasters.map { |b| b.profile[:polarity] }
      }
    end
    
    def polarity_weight(polarity)
      case polarity
      when :positive then 1.0
      when :negative then -1.0
      when :neutral then 0.0
      else 0.0
      end
    end
    
    def publish_superposition!(superposition)
      headers = Headers.build(
        mathematician: "tripartite",
        operation: :superposition,
        address: superposition[:combined],
        polarity: :neutral,
        epoch: @epoch,
        participants: @mathematician_keys.join(",")
      )
      
      @coordinator_nats.publish(
        "#{SUBJECT_PREFIX}.superposition.#{@epoch}",
        JSON.generate(superposition),
        header: headers
      )
    end
    
    def run!(steps = 12)
      steps.times { step! }
      self
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # QUARTO COMIC BOOK TRACER (String Diagram Visualization)
  # ═══════════════════════════════════════════════════════════════
  #
  # Generates Quarto-compatible markdown for "category theory tabloid"
  # Each epoch becomes a comic panel with string diagram notation
  
  module QuartoTracer
    def self.generate_panel(result, epoch)
      mathematician = result[:result][:mathematician] rescue result[:payload][:name]
      operation = result[:payload][:operation]
      address = result[:payload][:address]
      color = result[:payload][:color] || "#808080"
      
      <<~QUARTO
        ::: {.panel}
        ### Epoch #{epoch}: #{mathematician}
        
        ```{mermaid}
        flowchart LR
            subgraph "#{mathematician}"
                I[Input] -->|#{operation}| O[Output]
                O -.->|contravariant| U[Utility]
            end
            style I fill:#{color}
        ```
        
        **Address**: `#{address.join}`  
        **Operation**: `#{operation}`
        :::
      QUARTO
    end
    
    def self.generate_tabloid(system_results, title: "Category Theory Tabloid")
      panels = system_results.map.with_index do |step, i|
        step[:results].map { |r| generate_panel(r, step[:epoch]) }.join("\n\n")
      end
      
      <<~QUARTO
        ---
        title: "#{title}"
        format:
          html:
            theme: darkly
            mermaid:
              theme: dark
        ---
        
        # WORLD Broadcast: String Diagram Chronicle
        
        #{panels.join("\n\n---\n\n")}
        
        ## Superposition Analysis
        
        | Epoch | Combined Address | Conjugacy Class |
        |-------|------------------|-----------------|
        #{system_results.map { |s| "| #{s[:epoch]} | #{s[:superposition][:combined].join} | #{s[:superposition][:conjugacy].join} |" }.join("\n")}
      QUARTO
    end
  end
  
  # ═══════════════════════════════════════════════════════════════
  # MAIN ENTRY POINTS
  # ═══════════════════════════════════════════════════════════════
  
  def self.broadcast(mathematicians: [:ramanujan, :grothendieck, :euler], steps: 12, 
                     nats_url: "nats://127.0.0.1:4222", verbose: true, quarto: false)
    puts "╔═══════════════════════════════════════════════════════════════════════════════╗" if verbose
    puts "║  SYNADIA BROADCAST: NATS/JetStream WORLD Integration                          ║" if verbose
    puts "╚═══════════════════════════════════════════════════════════════════════════════╝" if verbose
    puts if verbose
    
    system = TripartiteSynadiaSystem.new(mathematicians, nats_url: nats_url)
    
    begin
      system.connect!
      
      if verbose
        puts "Connected to NATS at #{nats_url}"
        puts "Mathematicians: #{mathematicians.map { |m| WorldBroadcast::MATHEMATICIAN_PROFILES[m][:name] }.join(' ⊗ ')}"
        puts "JetStream stream: #{STREAM_CONFIG[:name]}"
        puts
        puts "Broadcasting #{steps} epochs..."
        puts "─" * 80
      end
      
      results = []
      steps.times do
        result = system.step!
        results << result
        
        if verbose
          addrs = result[:results].map { |r| r[:payload][:address].join }.join(' | ')
          sup = result[:superposition][:combined].join
          puts "Epoch #{result[:epoch].to_s.rjust(2)}: [#{addrs}] → superposition=#{sup}"
        end
      end
      
      if verbose
        puts
        puts "─" * 80
        puts "Subjects published:"
        result[:results].flat_map { |r| r[:subjects] }.uniq.first(5).each do |subj|
          puts "  #{subj}"
        end
        puts "  ..."
      end
      
      # Generate Quarto tabloid if requested
      if quarto
        tabloid = QuartoTracer.generate_tabloid(results)
        File.write("/tmp/world_broadcast_tabloid.qmd", tabloid)
        puts "\nQuarto tabloid written to /tmp/world_broadcast_tabloid.qmd" if verbose
      end
      
      { system: system, results: results }
    rescue Errno::ECONNREFUSED => e
      warn "⚠️  NATS connection refused at #{nats_url}"
      warn "   Start NATS server with: nats-server"
      warn "   Or install: brew install nats-server"
      raise
    ensure
      system.disconnect!
    end
  end
  
  # Demo mode (no NATS required - simulates messaging)
  def self.demo(mathematicians: [:depaiva, :hedges, :girard], steps: 6, verbose: true)
    puts "╔═══════════════════════════════════════════════════════════════════════════════╗" if verbose
    puts "║  SYNADIA BROADCAST DEMO (Simulated - no NATS required)                        ║" if verbose
    puts "╚═══════════════════════════════════════════════════════════════════════════════╝" if verbose
    puts if verbose
    
    # Use underlying WorldBroadcast but show NATS subject structure
    system = WorldBroadcast::TripartiteSystem.new(mathematicians)
    
    if verbose
      puts "Simulated NATS subjects:"
      puts "  world.broadcast.*     - Main broadcast"
      puts "  world.forward.*       - World action (covariant)"
      puts "  world.backward.*      - Coworld action (contravariant)"
      puts "  world.superposition.* - Tripartite combined state"
      puts "  world.sierpinski.*    - Gasket-indexed s-expressions"
      puts
      puts "Mathematicians: #{mathematicians.map { |m| WorldBroadcast::MATHEMATICIAN_PROFILES[m][:name] }.join(' ⊗ ')}"
      puts
      puts "Simulating #{steps} epochs..."
      puts "─" * 80
    end
    
    system.run!(steps)
    
    if verbose
      system.broadcast_log.each do |msg|
        addrs = msg[:agents].map { |a| a[:address].join }.join(' | ')
        sup = msg[:superposition][:combined].join
        
        # Show as NATS message format
        puts "NATS → world.superposition.#{msg[:epoch]}"
        puts "       addresses=[#{addrs}] → combined=#{sup}"
      end
      
      puts
      puts "─" * 80
      puts "To run with real NATS:"
      puts "  1. Install: brew install nats-server"
      puts "  2. Start:   nats-server"
      puts "  3. Run:     just synadia-broadcast"
    end
    
    system
  end
end

# Run if executed directly
if __FILE__ == $0
  if ARGV.include?("--demo")
    SynadiaBroadcast.demo
  else
    begin
      SynadiaBroadcast.broadcast
    rescue Errno::ECONNREFUSED
      puts "\nFalling back to demo mode..."
      SynadiaBroadcast.demo
    end
  end
end
