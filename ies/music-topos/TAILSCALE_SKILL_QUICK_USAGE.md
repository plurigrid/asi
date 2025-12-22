# Tailscale File Transfer Skill - Quick Usage Guide

## Installation Status

✅ **All installations complete and verified**

- Amp: `~/.local/share/amp/skills/tailscale_file_transfer.rb`
- Codex: `~/.topos/codex/codex-rs/core/src/skills/tailscale_file_transfer.rb`
- Music-Topos: `lib/tailscale_file_transfer_skill.rb` (source)
- Registry: `.ruler/skills/tailscale-file-transfer/` (documentation)

---

## Quick Start for Amp

### 1. In Amp Editor

```ruby
# Load the skill
require 'tailscale_file_transfer'

# Create instance
skill = TailscaleFileTransferSkill.new

# Send current buffer to collaborator
result = skill.play(
  file_path: buffer.file_path,
  recipient: "alice@coplay",
  strategy: :parallel
)

# Show result
puts "✓ Sent #{result[:bytes_sent]} bytes to #{result[:recipient]}"
```

### 2. Share a File

```ruby
# Share any file
result = skill.play(
  file_path: "/path/to/document.pdf",
  recipient: "collaborator@coplay",
  strategy: :sequential
)

# Get acknowledgment
ack = skill.coplay(
  transfer_id: result[:transfer_id],
  delivered: true,
  bytes_received: result[:bytes_sent],
  transfer_time: result[:transfer_time]
)

puts "Transfer complete. Utility: #{ack[:utility]}"
```

### 3. List Available Peers

```ruby
# Discover mesh peers
skill.discover_mesh_peers

# List all peers
skill.mesh_graph.each do |peer|
  status_icon = peer[:status] == :online ? "✓" : "✗"
  puts "#{status_icon} #{peer[:user]}@#{peer[:hostname]} (#{peer[:ip]})"
end
```

### 4. Check Transfer Stats

```ruby
# View all transfers
history = skill.transfer_history
history.each do |t|
  puts "#{t[:recipient]}: #{t[:bytes]} bytes, #{t[:throughput_kbps]} KB/s"
end

# Aggregate stats
stats = skill.transfer_stats
puts "Success Rate: #{stats[:success_rate]}%"
puts "Average Speed: #{stats[:average_throughput_kbps]} KB/s"
```

---

## Quick Start for Codex

### 1. In Codex Self-Rewriting Loop

```rust
// Load skill
use skills::tailscale_file_transfer;
let mut skill = TailscaleFileTransferSkill::new();

// Self-improve and share
let improved_code = self_improve_code();
improved_code.save("improved.rs").await;

// Share with team
skill.play(
  file_path: "improved.rs",
  recipient: "researcher@coplay",
  strategy: "parallel"
).await;
```

### 2. Broadcast to Multiple Peers

```rust
let improved = self_improve();
let recipients = vec!["alice@coplay", "bob@coplay", "charlie@coplay"];

for recipient in recipients {
  skill.play(
    file_path: &improved.path,
    recipient: recipient,
    strategy: "parallel"
  ).await;
}
```

### 3. With Codex Verification

```rust
// Generate code
let new_code = generate_new_code();

// Self-verify
let verified = verify_with_tests(&new_code).await;

// Share if verified
if verified.is_ok() {
  skill.play(
    file_path: &new_code.path,
    recipient: "production@coplay"
  ).await;
}
```

### 4. Monitor Transfer Progress

```rust
// Track transfer status
loop {
  let stats = skill.transfer_stats();

  if stats.success_rate > 95.0 {
    println!("✓ High reliability: {}%", stats.success_rate);
    break;
  }

  tokio::time::sleep(Duration::from_secs(1)).await;
}
```

---

## Quick Start for Music-Topos

### 1. Share Learned Model

```ruby
# Train color preference model
network = LearnablePLRNetwork.new(seed: 42)
train!(network, user_preferences)

# Save trained model
save_network(network, "learned_plr_network.jl")

# Share with collaborator
skill = TailscaleFileTransferSkill.new
result = skill.play(
  file_path: "learned_plr_network.jl",
  recipient: "alice@coplay",
  strategy: :parallel
)

# Notify on success
if result[:success]
  puts "✓ Model shared with Alice"
end
```

### 2. Collaborative Harmonic Analysis

```ruby
# Agent A analyzes
colors = load_test_colors
analysis_a = analyze_harmonics(colors)
save_json(analysis_a, "analysis_a.json")

# Send to merge agent
skill.play(file_path: "analysis_a.json", recipient: "bob@coplay")

# Bob receives and merges
merged_state = merge_crdt_states(
  load_crdt("analysis_a.json"),
  load_crdt("analysis_b.json")
)
```

### 3. Distribute Trained Network

```ruby
# After training improvements
if accuracy > 0.85
  # Save improved version
  save_network(improved_net, "v2_network.jl")

  # Share with all team members
  team = ["alice@coplay", "bob@coplay", "charlie@coplay"]
  team.each do |member|
    skill.play(file_path: "v2_network.jl", recipient: member, strategy: :parallel)
  end
end
```

---

## Strategy Selection

Choose the right strategy for your use case:

```ruby
# For document/config files (< 1MB)
strategy = :sequential

# For models and datasets (1-100MB)
strategy = :parallel

# For videos or large archives (> 100MB)
strategy = :adaptive

# Or auto-select
strategy = case File.size(file)
when 0...1_000_000
  :sequential
when 1_000_000...100_000_000
  :parallel
else
  :adaptive
end

result = skill.play(file_path: file, recipient: peer, strategy: strategy)
```

---

## Recipient Formats

Use whichever format is most convenient:

```ruby
# Preferred: Named identifier
skill.play(file_path: "file.txt", recipient: "alice@coplay")

# IP address
skill.play(file_path: "file.txt", recipient: "100.64.0.1")

# Hostname
skill.play(file_path: "file.txt", recipient: "alice-mbp")

# Resolve any format
recipient_ip = skill.resolve_recipient("alice@coplay")
# Returns: "100.64.0.1"
```

---

## Common Patterns

### Pattern 1: Verify Before Transfer

```ruby
# Check peer is online
if skill.mesh_graph.find { |p| p[:user] == "alice" }[:status] == :online
  result = skill.play(file_path: "file.txt", recipient: "alice@coplay")
else
  puts "✗ Alice is offline"
end
```

### Pattern 2: Batch Transfers

```ruby
# Transfer to multiple recipients
files = ["model.jl", "analysis.json", "results.csv"]
recipients = ["alice@coplay", "bob@coplay"]

files.each do |file|
  recipients.each do |recipient|
    skill.play(file_path: file, recipient: recipient, strategy: :parallel)
  end
end
```

### Pattern 3: Transfer with Verification

```ruby
# Open games composition
file_game = skill.create_open_game
verify_game = HashVerificationGame.new

composed = skill.compose_with_other_game(verify_game, composition_type: :sequential)
# File transfer → Hash verification → Success
```

### Pattern 4: Monitor Success Rate

```ruby
# Track reliability
skill.play(file_path: "data1.json", recipient: "alice@coplay")
skill.play(file_path: "data2.json", recipient: "alice@coplay")
skill.play(file_path: "data3.json", recipient: "alice@coplay")

stats = skill.transfer_stats
if stats[:success_rate] == 100.0
  puts "✓ Perfect reliability achieved"
end
```

---

## Error Handling

### Handle Transfer Failures

```ruby
result = skill.play(file_path: "file.txt", recipient: "alice@coplay")

if result[:success]
  puts "✓ Transfer successful (#{result[:bytes_sent]} bytes)"
else
  puts "✗ Transfer failed"
  # Retry with different strategy
  result = skill.play(file_path: "file.txt", recipient: "alice@coplay", strategy: :sequential)
end
```

### Handle Unknown Recipients

```ruby
recipient_ip = skill.resolve_recipient("alice@coplay")

if recipient_ip.nil?
  puts "✗ Unknown recipient"
  skill.discover_mesh_peers
  puts "Available peers: #{skill.mesh_graph.map { |p| p[:user] }.join(', ')}"
else
  result = skill.play(file_path: "file.txt", recipient: "alice@coplay")
end
```

### Check Network Status

```ruby
# Verify Tailscale is running
latency = skill.tailscale_api.peer_latency("100.64.0.1")

if latency.nil?
  puts "✗ Peer not reachable"
else
  puts "✓ Connection OK (#{latency}ms latency)"
end
```

---

## Testing

### Run Full Test Suite

```bash
cd /Users/bob/ies/music-topos
ruby lib/tailscale_file_transfer_skill.rb

# Expected output: ✓ All tests completed
```

### Test in REPL

```ruby
irb
require_relative 'lib/tailscale_file_transfer_skill'

skill = TailscaleFileTransferSkill.new
skill.discover_mesh_peers
puts skill.mesh_graph.size  # Should show: 5

result = skill.play(file_path: "/tmp/test.txt", recipient: "alice@coplay")
puts result[:success]  # Should show: true
```

---

## Quick Reference

| Task | Command |
|------|---------|
| **Load skill** | `require 'tailscale_file_transfer'` |
| **Create instance** | `skill = TailscaleFileTransferSkill.new` |
| **Discover peers** | `skill.discover_mesh_peers` |
| **List peers** | `skill.mesh_graph` |
| **Send file** | `skill.play(file_path: "...", recipient: "...")` |
| **Acknowledge** | `skill.coplay(transfer_id: "...", delivered: true, ...)` |
| **View history** | `skill.transfer_history` |
| **View stats** | `skill.transfer_stats` |
| **Create game** | `skill.create_open_game` |
| **Compose** | `skill.compose_with_other_game(other_game, ...)` |

---

## Performance Tips

1. **Use sequential for small files** (< 1MB)
2. **Use parallel for large files** (> 1MB, especially models)
3. **Use adaptive for unknown networks** (slow to investigate)
4. **Monitor success rate** to identify unreliable peers
5. **Batch transfers** to multiple recipients for efficiency

---

## Getting Help

- **Full Documentation**: `TAILSCALE_SKILL_DOCUMENTATION.md`
- **Quick Reference**: `TAILSCALE_SKILL_QUICKREF.md`
- **Installation Guide**: `.ruler/skills/tailscale-file-transfer/INSTALL.md`
- **Completion Report**: `TAILSCALE_SKILL_COMPLETION_REPORT.md`

---

**Ready to use!** Start with a simple file transfer:

```ruby
require 'tailscale_file_transfer'
skill = TailscaleFileTransferSkill.new
result = skill.play(file_path: "hello.txt", recipient: "alice@coplay")
puts "✓ Done! Transfer ID: #{result[:transfer_id]}"
```
