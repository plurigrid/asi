# lib/tailscale_file_transfer_skill.rb
#
# TAILSCALE FILE TRANSFER SKILL: Open Game Semantics for VPN File Sharing
#
# Integrates Tailscale mesh VPN with open games framework:
#   - Forward pass (play): Send file through Tailscale network
#   - Backward pass (coplay): Receive ack/error and propagate utility
#   - GF(3) trit semantics: Contravariant (sender), Ergodic (router), Covariant (receiver)
#
# Usage:
#   skill = TailscaleFileTransferSkill.new
#   skill.play(file_path: "document.pdf", recipient: "alice@coplay")
#   skill.coplay(ack: {delivered: true, bytes: 5242880})

require_relative 'hedges_open_games'
require_relative 'splitmix_ternary'
require 'socket'
require 'digest'
require 'json'
require 'fileutils'
require 'securerandom'

class TailscaleFileTransferSkill
  include HedgesOpenGames

  # ═══════════════════════════════════════════════════════════════════════════════
  # CONFIGURATION
  # ═══════════════════════════════════════════════════════════════════════════════

  DEFAULT_TAILSCALE_PORT = 22
  DEFAULT_TRANSFER_PORT = 9999
  CHUNK_SIZE = 1024 * 1024  # 1MB chunks
  TRANSFER_TIMEOUT = 300    # 5 minutes

  attr_reader :tailscale_api, :file_buffer, :transfer_log, :seed, :mesh_graph

  def initialize(tailscale_socket: nil, seed: SplitMixTernary::DEFAULT_SEED)
    @seed = seed
    @tailscale_socket = tailscale_socket
    @file_buffer = {}      # Buffer for in-transit files
    @transfer_log = []     # History of all transfers
    @mesh_graph = {}       # Tailscale network topology
    @pending_acks = {}     # Track outstanding acknowledgments

    initialize_tailscale_bridge
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # TAILSCALE BRIDGE: VPN Network Integration
  # ═══════════════════════════════════════════════════════════════════════════════

  def initialize_tailscale_bridge
    # Simulate Tailscale network discovery (would use tailscale CLI in production)
    @tailscale_api = TailscaleAPIBridge.new(@seed)
    discover_mesh_peers
  end

  def discover_mesh_peers
    # Discover available Tailscale peers in mesh network
    @mesh_graph = @tailscale_api.discover_peers
    puts "[TailscaleFileTransfer] Discovered #{@mesh_graph.size} peers in mesh network"
  end

  def resolve_recipient(recipient_identifier)
    # Resolve recipient identifier (user, hostname, or IP) to Tailscale IP
    case recipient_identifier
    when /^([a-zA-Z0-9.-]+)@coplay$/
      # Named coplay identifier
      username = $1
      @mesh_graph.find { |peer| peer[:user] == username }&.[](:ip)
    when /^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/
      # Already an IP
      recipient_identifier
    when /^100\./
      # Tailscale IP (100.x.y.z range)
      recipient_identifier
    else
      # Try hostname lookup
      @mesh_graph.find { |peer| peer[:hostname] == recipient_identifier }&.[](:ip)
    end
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # OPEN GAMES LENS: File Transfer as Bidirectional Optic
  # ═══════════════════════════════════════════════════════════════════════════════

  def create_file_transfer_lens
    Lens.new(
      name: "file_transfer",

      # Forward pass (play): Sender sends file through Tailscale
      forward: ->(context) {
        file_path = context[:file_path]
        recipient = context[:recipient]

        # Resolve recipient to Tailscale IP
        recipient_ip = resolve_recipient(recipient)

        raise "Unknown recipient: #{recipient}" unless recipient_ip

        # Read and hash file
        file_data = File.read(file_path)
        file_hash = Digest::SHA256.hexdigest(file_data)
        file_size = file_data.bytesize

        # Create transfer context
        transfer_id = generate_transfer_id

        {
          transfer_id: transfer_id,
          file_path: file_path,
          file_name: File.basename(file_path),
          file_size: file_size,
          file_hash: file_hash,
          sender_ip: get_local_tailscale_ip,
          recipient_ip: recipient_ip,
          recipient: recipient,
          timestamp: Time.now.to_i,
          status: :sending
        }
      },

      # Backward pass (coplay): Receiver sends ack back to sender
      backward: ->(context, ack_utility) {
        transfer_id = context[:transfer_id]
        recipient = context[:recipient]

        # Process acknowledgment from receiver
        success = ack_utility.is_a?(Hash) && ack_utility[:delivered]
        bytes_received = ack_utility[:bytes_received] || 0
        transfer_time = ack_utility[:transfer_time] || 0

        # Calculate quality metrics
        throughput = bytes_received > 0 ? bytes_received / (transfer_time + 0.001) : 0

        # Store in log
        @transfer_log << {
          transfer_id: transfer_id,
          recipient: recipient,
          success: success,
          bytes: bytes_received,
          time_seconds: transfer_time,
          throughput_kbps: (throughput / 1024).round(2),
          timestamp: Time.now.to_i
        }

        # Return utility score (0-1: failure to success)
        success ? 1.0 : 0.0
      },

      trit: 1  # Covariant (receiver gets the benefit)
    )
  end

  def create_receiver_coplay_lens
    Lens.new(
      name: "file_receiver",

      # Forward pass (play): Receiver prepares to accept file
      forward: ->(context) {
        transfer_id = context[:transfer_id]
        sender_ip = context[:sender_ip]
        expected_hash = context[:file_hash]
        expected_size = context[:file_size]

        # Create receive buffer
        @file_buffer[transfer_id] = {
          data: "",
          expected_size: expected_size,
          expected_hash: expected_hash,
          sender_ip: sender_ip,
          received_bytes: 0,
          start_time: Time.now
        }

        {
          transfer_id: transfer_id,
          status: :ready_to_receive,
          buffer_allocated: true
        }
      },

      # Backward pass (coplay): Verify received file and send ack
      backward: ->(context, received_data) {
        transfer_id = context[:transfer_id]
        buffer = @file_buffer[transfer_id]

        return 0.0 unless buffer

        # Accumulate received data
        buffer[:data] += received_data[:chunk] || ""
        buffer[:received_bytes] += received_data[:chunk_size] || 0

        # Check if complete
        if buffer[:received_bytes] >= buffer[:expected_size]
          actual_hash = Digest::SHA256.hexdigest(buffer[:data])
          transfer_complete = actual_hash == buffer[:expected_hash]
          transfer_time = Time.now - buffer[:start_time]

          if transfer_complete
            1.0  # Full success utility
          else
            0.5  # Partial utility (file corrupted)
          end
        else
          # Still receiving
          0.3 + (0.7 * buffer[:received_bytes] / buffer[:expected_size])
        end
      },

      trit: -1  # Contravariant (sender wants receiver to succeed)
    )
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # PLAY (Forward): Send File
  # ═══════════════════════════════════════════════════════════════════════════════

  def play(file_path:, recipient:, strategy: :sequential)
    unless File.exist?(file_path)
      raise "File not found: #{file_path}"
    end

    # Create context for lens
    context = {
      file_path: file_path,
      recipient: recipient,
      strategy: strategy
    }

    # Forward pass: prepare transfer
    lens = create_file_transfer_lens
    transfer_context = lens.forward.call(context)

    puts "\n[PLAY] File Transfer Initiated"
    puts "  Transfer ID: #{transfer_context[:transfer_id]}"
    puts "  File: #{transfer_context[:file_name]}"
    puts "  Size: #{format_bytes(transfer_context[:file_size])}"
    puts "  Recipient: #{recipient}"
    puts "  Recipient IP: #{transfer_context[:recipient_ip]}"

    # Execute transfer based on strategy
    result = execute_transfer(transfer_context, strategy)

    # Execute backward pass (coplay) to record transfer in log
    lens = create_file_transfer_lens
    ack_utility = {
      delivered: result[:success],
      bytes_received: result[:bytes_sent],
      transfer_time: result[:transfer_time]
    }
    lens.backward.call(transfer_context, ack_utility)

    {
      transfer_id: transfer_context[:transfer_id],
      file_path: file_path,
      recipient: recipient,
      bytes_sent: result[:bytes_sent],
      transfer_time: result[:transfer_time],
      success: result[:success],
      strategy: strategy
    }
  end

  def execute_transfer(transfer_context, strategy)
    transfer_id = transfer_context[:transfer_id]
    file_path = transfer_context[:file_path]
    file_size = transfer_context[:file_size]
    recipient_ip = transfer_context[:recipient_ip]

    file_data = File.read(file_path)
    start_time = Time.now
    bytes_sent = 0
    chunks_sent = 0

    case strategy
    when :sequential
      # Send in sequential chunks
      (0...file_size).step(CHUNK_SIZE) do |offset|
        chunk = file_data[offset...offset + CHUNK_SIZE]
        bytes_sent += chunk.bytesize
        chunks_sent += 1

        # Simulate network latency
        sleep(0.01)  # 10ms per chunk (tunable)

        progress = (bytes_sent.to_f / file_size * 100).round(1)
        print "\r  Sending: #{progress}% (#{format_bytes(bytes_sent)}/#{format_bytes(file_size)})"
      end

    when :parallel
      # Send in parallel chunks (would use multiple connections in production)
      num_threads = 4
      threads = []
      mutex = Mutex.new

      (0...num_threads).each do |thread_id|
        threads << Thread.new do
          offset = thread_id * CHUNK_SIZE
          while offset < file_size
            chunk = file_data[offset...offset + CHUNK_SIZE * num_threads]
            break unless chunk

            mutex.synchronize { bytes_sent += chunk.bytesize }
            sleep(0.005)  # Simulate per-chunk latency

            offset += CHUNK_SIZE * num_threads
          end
        end
      end

      threads.each(&:join)
      bytes_sent = file_size

    when :adaptive
      # Adaptive strategy: Start slow, speed up as connection stabilizes
      current_chunk_size = CHUNK_SIZE / 4

      (0...file_size).step(current_chunk_size) do |offset|
        chunk = file_data[offset...offset + current_chunk_size]
        bytes_sent += chunk.bytesize
        chunks_sent += 1

        # Adaptive chunk sizing (would be based on actual RTT in production)
        current_chunk_size = [current_chunk_size * 1.1, CHUNK_SIZE].min.to_i if chunks_sent % 10 == 0

        sleep(0.01 / (current_chunk_size.to_f / CHUNK_SIZE))
      end
    end

    transfer_time = Time.now - start_time
    puts "\n  ✓ Sent #{format_bytes(bytes_sent)} in #{transfer_time.round(2)}s"

    {
      bytes_sent: bytes_sent,
      transfer_time: transfer_time,
      success: bytes_sent == file_size,
      chunks: chunks_sent
    }
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # COPLAY (Backward): Receive Acknowledgment & Propagate Utility
  # ═══════════════════════════════════════════════════════════════════════════════

  def coplay(transfer_id:, delivered:, bytes_received: nil, transfer_time: nil)
    puts "\n[COPLAY] Acknowledgment Received"
    puts "  Transfer ID: #{transfer_id}"
    puts "  Delivered: #{delivered}"

    transfer_log_entry = @transfer_log.find { |t| t[:transfer_id] == transfer_id }
    return { utility: 0.0, reason: "Transfer not found" } unless transfer_log_entry

    bytes_received ||= transfer_log_entry[:bytes] || 0
    transfer_time ||= transfer_log_entry[:time_seconds] || 0

    # Calculate utility (composable with other games)
    base_utility = delivered ? 1.0 : 0.0

    # Quality metrics
    quality_bonus = 0.0
    quality_bonus += 0.1 if transfer_time < 5.0  # Fast transfer
    quality_bonus += 0.05 if bytes_received > 0.95 * transfer_log_entry[:bytes]  # Complete

    utility = [base_utility + quality_bonus, 1.0].min

    puts "  Utility Score: #{utility.round(3)}"
    puts "  Quality Bonus: #{quality_bonus.round(3)}"

    {
      transfer_id: transfer_id,
      delivered: delivered,
      utility: utility,
      quality_bonus: quality_bonus,
      backward_propagation: {
        sender_satisfaction: utility,
        network_efficiency: (bytes_received.to_f / (transfer_time + 0.001)) / (1024 * 1024)
      }
    }
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # COMPOSITION: Compose File Transfer with Other Games
  # ═══════════════════════════════════════════════════════════════════════════════

  def create_open_game
    transfer_lens = create_file_transfer_lens

    OpenGame.new(
      name: "tailscale_file_transfer",
      lens: transfer_lens,
      strategy_space: [:sequential, :parallel, :adaptive],
      utility_fn: ->(strategy, outcome) {
        # Utility increases with success and decreases with time
        base = outcome[:status] == :sent ? 1.0 : 0.0
        time_penalty = [0.5 - (outcome[:transfer_time] / 60.0), 0.0].max  # 1min = max penalty
        speed_bonus = [outcome[:transfer_time].zero? ? 0 : 0.2, 0.0].max

        base - time_penalty + speed_bonus
      },
      seed: @seed,
      trit: 1  # Covariant (receiver perspective)
    )
  end

  def compose_with_other_game(other_game, composition_type: :sequential)
    file_transfer_game = create_open_game

    case composition_type
    when :sequential
      file_transfer_game >> other_game
    when :parallel
      file_transfer_game * other_game
    else
      raise "Unknown composition type: #{composition_type}"
    end
  end

  # ═══════════════════════════════════════════════════════════════════════════════
  # UTILITIES & HELPERS
  # ═══════════════════════════════════════════════════════════════════════════════

  def generate_transfer_id
    "transfer_#{Time.now.to_i}_#{SecureRandom.hex(4)}"
  end

  def get_local_tailscale_ip
    # Would query `tailscale ip -4` in production
    "100.64.0.1"
  end

  def format_bytes(bytes)
    case bytes
    when 0...1024
      "#{bytes}B"
    when 1024...1024**2
      "#{(bytes / 1024.0).round(1)}KB"
    when 1024**2...1024**3
      "#{(bytes / (1024**2).to_f).round(1)}MB"
    else
      "#{(bytes / (1024**3).to_f).round(1)}GB"
    end
  end

  def transfer_history
    @transfer_log
  end

  def transfer_stats
    return {} if @transfer_log.empty?

    total_bytes = @transfer_log.sum { |t| t[:bytes] || 0 }
    total_time = @transfer_log.sum { |t| t[:time_seconds] || 0 }
    successful = @transfer_log.count { |t| t[:success] }

    {
      total_transfers: @transfer_log.size,
      successful_transfers: successful,
      success_rate: (successful.to_f / @transfer_log.size * 100).round(1),
      total_bytes: total_bytes,
      total_time: total_time,
      average_throughput_kbps: total_time > 0 ? ((total_bytes / 1024.0) / total_time).round(2) : 0,
      average_transfer_size: (total_bytes.to_f / @transfer_log.size).round(0)
    }
  end
end

# ═══════════════════════════════════════════════════════════════════════════════
# TAILSCALE API BRIDGE: Simulated Mesh Network Discovery
# ═══════════════════════════════════════════════════════════════════════════════

class TailscaleAPIBridge
  attr_reader :seed, :peers

  def initialize(seed = SplitMixTernary::DEFAULT_SEED)
    @seed = seed
    @peers = []
    initialize_mock_network
  end

  def initialize_mock_network
    # Create a mock Tailscale mesh network
    @peers = [
      { user: "alice", hostname: "alice-mbp", ip: "100.64.0.1", status: :online },
      { user: "bob", hostname: "bob-linux", ip: "100.64.0.2", status: :online },
      { user: "charlie", hostname: "charlie-iphone", ip: "100.64.0.3", status: :online },
      { user: "diana", hostname: "diana-vm", ip: "100.64.0.4", status: :offline },
      { user: "eve", hostname: "eve-server", ip: "100.64.0.5", status: :online }
    ]
  end

  def discover_peers
    @peers
  end

  def peer_latency(peer_ip)
    # Simulate latency (in milliseconds)
    case peer_ip
    when "100.64.0.1" then 5    # Local network
    when "100.64.0.2" then 15   # Same region
    when "100.64.0.3" then 45   # Different region
    when "100.64.0.5" then 100  # Remote server
    else 50
    end
  end

  def peer_bandwidth(peer_ip)
    # Simulate available bandwidth (in Mbps)
    case peer_ip
    when "100.64.0.1" then 1000  # Gigabit
    when "100.64.0.2" then 500   # High speed
    when "100.64.0.3" then 100   # Medium
    when "100.64.0.5" then 10    # Limited
    else 50
    end
  end
end

# ═══════════════════════════════════════════════════════════════════════════════
# TEST SUITE
# ═══════════════════════════════════════════════════════════════════════════════

if __FILE__ == $0
  puts "╔" + "═"*78 + "╗"
  puts "║" + " "*15 + "TAILSCALE FILE TRANSFER SKILL TEST SUITE" + " "*23 + "║"
  puts "╚" + "═"*78 + "╝"

  # Create test file
  test_file = "/tmp/tailscale_test_file.txt"
  File.write(test_file, "Hello from Tailscale! " * 1000)

  # Initialize skill
  skill = TailscaleFileTransferSkill.new

  puts "\n1. Testing PLAY: Sequential file transfer"
  result = skill.play(
    file_path: test_file,
    recipient: "alice@coplay",
    strategy: :sequential
  )
  puts "   Result: #{result.inspect}"

  puts "\n2. Testing COPLAY: Acknowledgment and utility propagation"
  ack = skill.coplay(
    transfer_id: result[:transfer_id],
    delivered: true,
    bytes_received: result[:bytes_sent],
    transfer_time: result[:transfer_time]
  )
  puts "   Utility: #{ack[:utility].round(3)}"

  puts "\n3. Testing transfer statistics"
  stats = skill.transfer_stats
  puts "   Success Rate: #{stats[:success_rate]}%"
  puts "   Average Throughput: #{stats[:average_throughput_kbps]} KB/s"

  puts "\n4. Testing different strategies"
  [:parallel, :adaptive].each do |strategy|
    result = skill.play(
      file_path: test_file,
      recipient: "bob@coplay",
      strategy: strategy
    )
    puts "   #{strategy}: #{skill.send(:format_bytes, result[:bytes_sent])} in #{result[:transfer_time].round(2)}s"
  end

  puts "\n5. Testing mesh network topology"
  peers = skill.mesh_graph
  puts "   Discovered #{peers.size} peers:"
  peers.each { |p| puts "     - #{p[:user]}@#{p[:hostname]} (#{p[:ip]}) [#{p[:status]}]" }

  puts "\n✓ All tests completed"

  # Cleanup
  File.delete(test_file) if File.exist?(test_file)
end
