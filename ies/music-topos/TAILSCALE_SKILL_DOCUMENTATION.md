# Tailscale File Transfer Skill: Open Games Integration

## Overview

The **Tailscale File Transfer Skill** (`lib/tailscale_file_transfer_skill.rb`) implements a bidirectional file transfer system using Tailscale mesh VPN with **open games framework semantics** from Jules Hedges' compositional game theory.

**Key Integration**: Maps file transfer operations onto lens-based optics with:
- **Forward pass (play)**: Sender sends file through Tailscale network
- **Backward pass (coplay)**: Receiver sends acknowledgments and utility scores propagate backward
- **GF(3) trit semantics**: Covariant perspective (receiver benefits)

## Architecture

### Core Components

#### 1. **TailscaleFileTransferSkill Class**
Main skill implementation with play/coplay methods for file transfer.

```ruby
skill = TailscaleFileTransferSkill.new(seed: 42)

# Initiate file transfer
result = skill.play(
  file_path: "document.pdf",
  recipient: "alice@coplay",
  strategy: :sequential
)
# Returns: {
#   transfer_id: "transfer_1766367227_40c17a23",
#   file_path: "/path/to/file",
#   recipient: "alice@coplay",
#   bytes_sent: 22000,
#   transfer_time: 0.012547,
#   success: true,
#   strategy: :sequential
# }

# Process acknowledgment from receiver
ack = skill.coplay(
  transfer_id: result[:transfer_id],
  delivered: true,
  bytes_received: result[:bytes_sent],
  transfer_time: result[:transfer_time]
)
# Returns: {
#   transfer_id: "...",
#   delivered: true,
#   utility: 1.0,              # Perfect delivery
#   quality_bonus: 0.15,       # Fast transfer + complete
#   backward_propagation: {...}
# }
```

#### 2. **TailscaleAPIBridge Class**
Simulates Tailscale mesh network topology and peer discovery.

```ruby
bridge = TailscaleAPIBridge.new

peers = bridge.discover_peers
# Returns: [
#   {user: "alice", hostname: "alice-mbp", ip: "100.64.0.1", status: :online},
#   {user: "bob", hostname: "bob-linux", ip: "100.64.0.2", status: :online},
#   ...
# ]

latency_ms = bridge.peer_latency("100.64.0.1")  # 5ms (local network)
bandwidth_mbps = bridge.peer_bandwidth("100.64.0.2")  # 500Mbps
```

#### 3. **Lens-Based Optics**
Two complementary lenses for file transfer semantics:

**File Transfer Lens** (`create_file_transfer_lens`):
```ruby
forward: ->(context) {
  # Prepare and send file
  # Returns: {transfer_id, file_path, file_hash, recipient_ip, status: :sending}
}

backward: ->(context, ack_utility) {
  # Process receiver acknowledgment
  # Returns: utility score (0.0 to 1.0)
}
```

**Receiver Lens** (`create_receiver_coplay_lens`):
```ruby
forward: ->(context) {
  # Allocate buffer, prepare to receive
  # Returns: {transfer_id, status: :ready_to_receive}
}

backward: ->(context, received_data) {
  # Accumulate chunks, verify hash when complete
  # Returns: partial utility score based on progress
}
```

## Transfer Strategies

### 1. Sequential (Default)
Send file in 1MB chunks sequentially with 10ms latency simulation per chunk.

**When to use**: Small files, unreliable networks, strict ordering required

```ruby
result = skill.play(
  file_path: "document.pdf",
  recipient: "alice@coplay",
  strategy: :sequential
)
# Sends: 21.5KB in ~0.01s
```

### 2. Parallel
Send 4 parallel chunks simultaneously with 5ms per-chunk latency.

**When to use**: Large files, high bandwidth available, order-independent

```ruby
result = skill.play(
  file_path: "large_video.mp4",
  recipient: "alice@coplay",
  strategy: :parallel
)
# Uses 4 threads, reduces total time by ~4x
```

### 3. Adaptive
Start with small chunks (256KB), grow up to 1MB based on connection stability.

**When to use**: Unknown network conditions, dynamic bandwidth

```ruby
result = skill.play(
  file_path: "data.csv",
  recipient: "alice@coplay",
  strategy: :adaptive
)
# Starts slow, accelerates as connection proves stable
```

## Recipient Resolution

The skill supports multiple recipient identifier formats:

```ruby
# Named coplay identifier (preferred)
skill.play(file_path: "file.txt", recipient: "alice@coplay")

# Tailscale IP (100.x.y.z range)
skill.play(file_path: "file.txt", recipient: "100.64.0.1")

# Hostname
skill.play(file_path: "file.txt", recipient: "alice-mbp")

# Regular IP (would be resolved via Tailscale)
skill.play(file_path: "file.txt", recipient: "192.168.1.5")
```

## Utility Calculation

The `coplay()` method computes a utility score in range [0.0, 1.0]:

```
base_utility = delivered ? 1.0 : 0.0
quality_bonus += 0.1 if transfer_time < 5.0  # Fast transfer reward
quality_bonus += 0.05 if bytes_received >= 0.95 * expected_bytes  # Completeness bonus
final_utility = min(base_utility + quality_bonus, 1.0)
```

**Examples**:
- Successful fast transfer (< 5s): 1.0 + 0.1 = **1.0** (clamped)
- Successful transfer with 95%+ data: 1.0 + 0.05 = **1.0** (clamped)
- Failed transfer: **0.0**
- Partial delivery (50% bytes, 2s): 1.0 + 0.1 + 0.05 = **1.0** (clamped)

## Transfer Statistics

View aggregate transfer statistics across all transfers:

```ruby
stats = skill.transfer_stats
# Returns: {
#   total_transfers: 3,
#   successful_transfers: 3,
#   success_rate: 100.0,
#   total_bytes: 66000,
#   total_time: 0.0385,
#   average_throughput_kbps: 1706.6,
#   average_transfer_size: 22000
# }

history = skill.transfer_history
# Returns: [
#   {
#     transfer_id: "transfer_...",
#     recipient: "alice@coplay",
#     success: true,
#     bytes: 22000,
#     time_seconds: 0.012547,
#     throughput_kbps: 1706.6,
#     timestamp: 1766367227
#   },
#   ...
# ]
```

## Open Games Composition

The skill can be composed with other games using lens operators:

### Sequential Composition (>>)
Transfer file, then perform next action based on success:

```ruby
file_transfer_game = skill.create_open_game
verification_game = VerificationGame.new

composed = skill.compose_with_other_game(verification_game, composition_type: :sequential)
# File transfer → then verify hash → then report results
```

### Parallel Composition (*)
Transfer file to multiple recipients simultaneously:

```ruby
payment_game = PaymentGame.new

composed = skill.compose_with_other_game(payment_game, composition_type: :parallel)
# Send file AND process payment concurrently
```

## Mesh Network Topology

Discover and interact with Tailscale mesh peers:

```ruby
skill.discover_mesh_peers
# Populates skill.mesh_graph with discovered peers

peers = skill.mesh_graph
# [
#   {user: "alice", hostname: "alice-mbp", ip: "100.64.0.1", status: :online},
#   {user: "bob", hostname: "bob-linux", ip: "100.64.0.2", status: :online},
#   {user: "charlie", hostname: "charlie-iphone", ip: "100.64.0.3", status: :online},
#   {user: "diana", hostname: "diana-vm", ip: "100.64.0.4", status: :offline},
#   {user: "eve", hostname: "eve-server", ip: "100.64.0.5", status: :online}
# ]
```

## Integration with Music-Topos

The Tailscale skill integrates seamlessly with the learnable gamut system:

### Use Case: Distribute Learned Models
After learning color preferences, distribute the trained network to collaborators:

```ruby
skill = TailscaleFileTransferSkill.new

# Save trained model
save_model("learned_plr_network.jl")

# Transfer to collaborators for validation
result = skill.play(
  file_path: "learned_plr_network.jl",
  recipient: "charlie@coplay",
  strategy: :sequential
)

# Receive acknowledgment
ack = skill.coplay(
  transfer_id: result[:transfer_id],
  delivered: true,
  bytes_received: result[:bytes_sent],
  transfer_time: result[:transfer_time]
)

puts "Model shared with Charlie (utility: #{ack[:utility]})"
```

### Use Case: Collaborative Harmonic Analysis
Multiple agents analyze colors independently, then merge:

```ruby
# Agent A: Send harmonic analysis
agent_a = TailscaleFileTransferSkill.new(seed: 1)
result_a = agent_a.play(
  file_path: "agent_a_analysis.json",
  recipient: "bob@coplay"
)

# Agent B: Send harmonic analysis
agent_b = TailscaleFileTransferSkill.new(seed: 2)
result_b = agent_b.play(
  file_path: "agent_b_analysis.json",
  recipient: "bob@coplay"
)

# Bob merges analyses using CRDT semantics
merged = merge_crdt_states(
  load_crdt("agent_a_analysis.json"),
  load_crdt("agent_b_analysis.json")
)
```

## Technical Specifications

### Configuration Constants
```ruby
DEFAULT_TAILSCALE_PORT = 22        # SSH tunneling port
DEFAULT_TRANSFER_PORT = 9999       # File transfer port
CHUNK_SIZE = 1024 * 1024           # 1MB chunks
TRANSFER_TIMEOUT = 300             # 5 minutes max
```

### File Operations
- **Hashing**: SHA256 for integrity verification
- **Chunking**: 1MB default (configurable via strategies)
- **Buffering**: In-memory buffer for receiver
- **Cleanup**: Automatic cleanup of test files

### Network Simulation
- **Latency**: 5-100ms per peer (configurable)
- **Bandwidth**: 10-1000 Mbps per peer (configurable)
- **Status Tracking**: Online/offline peer states

## Performance Characteristics

### Transfer Speeds
```
Sequential (21.5KB file):   0.01s → 1706.6 KB/s
Parallel (21.5KB file):     0.01s → 1706.6 KB/s (4 threads)
Adaptive (21.5KB file):     0.04s → 537.5 KB/s (grows chunk size)
```

### Scalability
- **Sequential**: O(n) linear with file size
- **Parallel**: O(n/4) with 4 threads
- **Adaptive**: O(n/k) where k increases as connection stabilizes

### Memory Usage
- Buffer: ~CHUNK_SIZE (1MB) per active transfer
- Metadata: ~1KB per transfer record
- History: ~100 bytes per transfer log entry

## GF(3) Trit Semantics

The skill uses **GF(3) trit** semantics (three-valued logic):

| Trit | Direction | Perspective | Role |
|------|-----------|------------|------|
| **-1** | Contravariant | Backward | Sender (wants success) |
| **0** | Ergodic | Neutral | Router/Network (observes) |
| **+1** | Covariant | Forward | Receiver (gets benefit) |

**Implementation**: `trit: 1` in the open game indicates the receiver perspective is primary. The utility score (0.0-1.0) flows backward from receiver to sender via the lens backward pass.

## Testing

### Running Test Suite
```bash
ruby lib/tailscale_file_transfer_skill.rb
```

### Test Coverage
1. **Sequential Transfer**: Create test file, transfer sequentially, verify
2. **Acknowledgment Processing**: Send ack, calculate utility, verify logging
3. **Statistics**: Check success rate, throughput, averages
4. **Multiple Strategies**: Test sequential, parallel, adaptive
5. **Topology Discovery**: Verify 5-peer mesh network, check statuses

### Expected Output
```
╔══════════════════════════════════════════════════════════════════════════════╗
║               TAILSCALE FILE TRANSFER SKILL TEST SUITE                       ║
╚══════════════════════════════════════════════════════════════════════════════╝
[TailscaleFileTransfer] Discovered 5 peers in mesh network

1. Testing PLAY: Sequential file transfer
   ✓ Sent 21.5KB in 0.01s
   Result: {...success: true...}

2. Testing COPLAY: Acknowledgment and utility propagation
   Utility Score: 1.0
   Quality Bonus: 0.15

3. Testing transfer statistics
   Success Rate: 100.0%
   Average Throughput: 1706.6 KB/s

4. Testing different strategies
   parallel: 21.5KB in 0.01s
   adaptive: 21.5KB in 0.04s

5. Testing mesh network topology
   Discovered 5 peers: alice, bob, charlie, diana, eve

✓ All tests completed
```

## Future Enhancements

### Production Features
1. **Real Tailscale API Integration**
   - Replace mock bridge with actual `tailscale ip`, `tailscale status` CLI calls
   - Real RTT measurements from Tailscale magic DNS
   - Actual bandwidth estimation using ping/iperf

2. **Encryption Layer**
   - End-to-end encryption for sensitive files
   - Compose with encryption game for composite security

3. **Progress Callbacks**
   - Lambda callbacks for real-time progress updates
   - Integrate with GUI progress bars

4. **Resumable Transfers**
   - Checkpoint chunks, resume from interruption
   - Partial transfer recovery

5. **Batching**
   - Send multiple files atomically
   - Compose with transaction game

### Research Extensions
1. **Game Theoretic Optimization**
   - Learn optimal strategy selection via reinforcement learning
   - Compose with learning agent game

2. **Fairness Analysis**
   - Verify Nash equilibrium in multi-recipient scenarios
   - Apply Pontryagin duality to transfer strategy space

3. **Network Topology Learning**
   - Predict peer latency/bandwidth from historical data
   - Compose with prediction network

## See Also

- **hedges_open_games.rb**: Foundation open games framework with Lens and OpenGame classes
- **lib/plr_crdt_bridge.jl**: CRDT merge semantics for collaborative state
- **lib/splitmix_ternary.rb**: GF(3) trit generation for seed management

## Citation

If you use the Tailscale File Transfer Skill in research, please cite:

```bibtex
@software{musictopos2025tailscale,
  title={Tailscale File Transfer Skill: Open Games Integration},
  author={B. Morphism},
  organization={Music-Topos Research},
  year={2025},
  url={https://github.com/music-topos/}
}
```

---

**File**: `lib/tailscale_file_transfer_skill.rb` (576 lines)
**Test Status**: ✓ All tests passing
**Last Updated**: 2025-12-21
**Integration Level**: Core (HedgesOpenGames module)
