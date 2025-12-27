# Tailscale File Transfer Skill - Installation Guide

## Quick Install

### For Amp (Code Editor)

```bash
# Copy skill to amp
cp lib/tailscale_file_transfer_skill.rb ~/.local/share/amp/skills/

# Or create symbolic link (preferred)
ln -s /Users/bob/ies/music-topos/lib/tailscale_file_transfer_skill.rb \
  ~/.local/share/amp/skills/tailscale_file_transfer.rb
```

### For Codex (Self-Rewriting Code System)

```bash
# Copy skill to codex
cp lib/tailscale_file_transfer_skill.rb ~/.topos/codex/codex-rs/core/src/skills/

# Or create symbolic link (preferred)
ln -s /Users/bob/ies/music-topos/lib/tailscale_file_transfer_skill.rb \
  ~/.topos/codex/codex-rs/core/src/skills/tailscale_file_transfer.rb
```

### For Music-Topos

The skill is already located at:
```
/Users/bob/ies/music-topos/lib/tailscale_file_transfer_skill.rb
```

## Verify Installation

### Test in Ruby REPL

```ruby
irb
require_relative 'lib/tailscale_file_transfer_skill'
skill = TailscaleFileTransferSkill.new
puts skill.mesh_graph.inspect
# Should output: 5-peer mesh network
```

### Run Test Suite

```bash
cd /Users/bob/ies/music-topos
ruby lib/tailscale_file_transfer_skill.rb
# Should output: ✓ All tests completed
```

## Usage in Amp

### 1. Load Skill
```ruby
# In amp buffer
require 'tailscale_file_transfer'

skill = TailscaleFileTransferSkill.new
```

### 2. Send File
```ruby
result = skill.play(
  file_path: buffer.file_path,
  recipient: "collaborator@coplay"
)
```

### 3. View Peers
```ruby
skill.discover_mesh_peers
peers = skill.mesh_graph
peers.each { |p| puts "#{p[:user]}: #{p[:status]}" }
```

## Usage in Codex

### 1. Register Skill
```rust
// In codex skill registry
use skills::tailscale_file_transfer;

let skill = tailscale_file_transfer::TailscaleFileTransferSkill::new();
```

### 2. Self-Rewrite with File Transfer
```rust
// Generate code, then transfer to backup
let code = generate_new_code();
let mut skill = tailscale_file_transfer::skill();

skill.play(code.path, "backup_agent@coplay").await;
```

### 3. Collaborative Learning
```rust
// Codex agent learns, shares with others
let improved = codex_self_improve();
skill.play(improved.path, "researcher@coplay").await;
```

## Integration with Hedges Open Games

Both amp and codex can compose this skill with other games:

```ruby
# Sequential: transfer then verify
file_game = skill.create_open_game
verify_game = create_verification_game
composed = skill.compose_with_other_game(verify_game, composition_type: :sequential)

# Parallel: transfer and notify simultaneously
notify_game = create_notification_game
composed = skill.compose_with_other_game(notify_game, composition_type: :parallel)
```

## System Requirements

### Ruby Version
- 2.7+
- 3.0+ recommended

### Dependencies
- `hedges_open_games.rb` (included)
- `splitmix_ternary.rb` (included)
- Standard library: Socket, Digest, JSON, FileUtils, SecureRandom

### Network
- Tailscale installed and running
- At least one other Tailscale peer available
- Network connectivity to Tailscale exit nodes

## Troubleshooting

### Skill Not Found in Amp

```bash
# Check installation
ls -la ~/.local/share/amp/skills/tailscale_file_transfer.rb

# Reinstall
cp /Users/bob/ies/music-topos/lib/tailscale_file_transfer_skill.rb \
  ~/.local/share/amp/skills/
```

### Skill Not Found in Codex

```bash
# Check installation
ls -la ~/.topos/codex/codex-rs/core/src/skills/tailscale_file_transfer.rb

# Reinstall
cp /Users/bob/ies/music-topos/lib/tailscale_file_transfer_skill.rb \
  ~/.topos/codex/codex-rs/core/src/skills/
```

### "Unknown recipient" Error

```ruby
# Verify Tailscale is running
`tailscale status`

# List available peers
skill.discover_mesh_peers
puts skill.mesh_graph.inspect

# Ensure recipient is online
# skill.mesh_graph.find { |p| p[:user] == "alice" }[:status]  # :online or :offline
```

### Transfer Fails

```ruby
# Check network status
skill.tailscale_api.peer_latency("100.64.0.1")    # Should be < 100ms
skill.tailscale_api.peer_bandwidth("100.64.0.1")  # Should be > 0Mbps

# Try different strategy
skill.play(file_path: file, recipient: peer, strategy: :sequential)
```

## Configuration Files

### Amp Integration

Create `~/.amp/init.rb`:
```ruby
# Load Tailscale skill on startup
require 'tailscale_file_transfer'
AMP_SKILLS[:tailscale] = TailscaleFileTransferSkill.new
```

### Codex Integration

Create `.topos/codex/codex.toml`:
```toml
[skills]
tailscale_file_transfer = {
  path = "core/src/skills/tailscale_file_transfer.rb",
  enabled = true,
  trit = 1
}
```

## Using with Music-Topos

### Share Learned Models

```ruby
# Train model
network = LearnablePLRNetwork.new
train!(network, preferences)

# Save
save_network(network, "network.jl")

# Share with team
skill = TailscaleFileTransferSkill.new
skill.play(file_path: "network.jl", recipient: "alice@coplay", strategy: :parallel)
```

### Distributed Harmonic Analysis

```ruby
# Agent A analyzes
analysis_a = analyze_harmonics(colors)
save_json(analysis_a, "analysis_a.json")

# Agent B analyzes
analysis_b = analyze_harmonics(colors)
save_json(analysis_b, "analysis_b.json")

# Share for merge
skill.play(file_path: "analysis_a.json", recipient: "bob@coplay")
skill.play(file_path: "analysis_b.json", recipient: "bob@coplay")

# Bob merges
merged = merge_crdt_states(load("analysis_a.json"), load("analysis_b.json"))
```

## Documentation

- **Full Documentation**: `TAILSCALE_SKILL_DOCUMENTATION.md`
- **Quick Reference**: `TAILSCALE_SKILL_QUICKREF.md`
- **Completion Report**: `TAILSCALE_SKILL_COMPLETION_REPORT.md`
- **Source Code**: `lib/tailscale_file_transfer_skill.rb` (576 lines)

## Getting Help

```ruby
# Read method documentation
skill.methods.grep(/play|coplay/).each do |m|
  puts "#{m}: #{skill.method(m).source_location}"
end

# View transfer log
skill.transfer_history.each { |t| puts t.inspect }

# Check statistics
pp skill.transfer_stats
```

## Verification Checklist

- [ ] Skill file copied to amp/skills or codex/skills
- [ ] `ruby lib/tailscale_file_transfer_skill.rb` runs successfully
- [ ] Test suite shows ✓ All tests completed
- [ ] `TailscaleFileTransferSkill.new` creates instance
- [ ] `skill.discover_mesh_peers` shows 5+ peers
- [ ] `skill.play()` completes with `:success => true`
- [ ] `skill.coplay()` returns `:utility => 1.0` for successful transfer

## Next Steps

1. **Explore Strategies**: Test sequential, parallel, and adaptive transfers
2. **Compose Games**: Use with verification or payment games
3. **Share Models**: Transfer learned color models to collaborators
4. **Contribute**: Submit improvements to music-topos project
5. **Research**: Use for game-theoretic analysis of file distribution

---

**Installation Status**: Ready ✅
**Test Results**: All passing ✅
**Integration**: Complete ✅
