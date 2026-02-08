# CRDT Skill

**Status**: ✅ Production Ready
**Framework**: Jules Hedges' Compositional Game Theory
**Language**: Ruby
**Installations**: Amp, Codex, Music-Topos

## Quick Start

```ruby
require 'crdt_skill'

skill = CRDTSkill.new

# Create a CRDT
skill.create("counter", :pn_counter, "replica-1")

# Mutate it
skill.mutate("counter", :increment, 5)
skill.mutate("counter", :decrement, 2)

# Query the value
result = skill.query("counter")
# => { value: 3, ... }
```

## Core Features

- **5 CRDT Types**: LWWRegister, GCounter, PNCounter, ORSet, TextCRDT
- **Verified Properties**: Idempotence, Commutativity, Associativity
- **Open Games Interface**: play() / coplay() semantics
- **Bidirectional Optics**: Forward/backward passes
- **Merge Verification**: Automatic consistency checking
- **Vector Clocks**: Causality tracking

## Installation

### For Amp
```bash
ln -s /Users/bob/ies/music-topos/lib/crdt_skill.rb \
  ~/.local/share/amp/skills/crdt_skill.rb
```

### For Codex
```bash
ln -s /Users/bob/ies/music-topos/lib/crdt_skill.rb \
  ~/.topos/codex/codex-rs/core/src/skills/crdt_skill.rb
```

### For Music-Topos
Located at: `/Users/bob/ies/music-topos/lib/crdt_skill.rb`

## CRDT Types

### LWW Register
Last-Write-Wins register for simple mutable state.
```ruby
skill.create("state", :lww_register)
skill.mutate("state", :set, 42)
```

### G-Counter
Grow-only counter (increment only).
```ruby
skill.create("views", :g_counter)
skill.mutate("views", :increment, 1)
```

### PN-Counter
Positive-Negative counter (increment and decrement).
```ruby
skill.create("balance", :pn_counter)
skill.mutate("balance", :increment, 100)
skill.mutate("balance", :decrement, 30)
```

### OR-Set
Observed-Remove set for unordered collections.
```ruby
skill.create("members", :or_set)
skill.mutate("members", :add, "alice")
skill.mutate("members", :add, "bob")
```

### Text CRDT
Character-based CRDT for text editing.
```ruby
skill.create("document", :text_crdt)
skill.mutate("document", :insert, 0, "H")
skill.mutate("document", :insert, 1, "i")
```

## Merge Operations

```ruby
# Create two CRDTs
skill.create("set1", :or_set)
skill.mutate("set1", :add, "apple")

skill.create("set2", :or_set)
skill.mutate("set2", :add, "banana")

# Merge them
result = skill.merge("set1", "set2")
# Result in "set1_merged"

# Verify properties
skill.verify_idempotence(crdt1, crdt2)
skill.verify_commutativity("set1", "set2")
skill.verify_associativity("c1", "c2", "c3")
```

## Open Games API

### Forward Pass (play)
```ruby
result = skill.play(
  crdt_name: "shared_state",
  operations: [
    {op: :add, value: "x"},
    {op: :add, value: "y"}
  ]
)
```

### Backward Pass (coplay)
```ruby
ack = skill.coplay(
  transfer_id: result[:transfer_id],
  acknowledged: true,
  consistency_verified: true
)
# => { success: true, utility: 1.0, ... }
```

## Statistics

```ruby
stats = skill.statistics
# => {
#   total_crdts: 8,
#   total_merges: 2,
#   total_operations: 27,
#   merge_success_rate: 100.0,
#   avg_merge_time: 0.02
# }
```

## Testing

```bash
ruby lib/crdt_skill.rb

# Output:
# ✓ Test 1: Create and Query
# ✓ Test 2: GCounter increment
# ✓ Test 3: ORSet merge
# ✓ Test 4: Idempotence verified
# ✓ Test 5: Play/Coplay semantics
# ✓ All tests passed!
```

## Integration Examples

### With Music-Topos Distributed Learning
```ruby
# Share color preferences
skill.create("preferences", :or_set, "agent-a")
["red", "green", "blue"].each { |c| skill.mutate("preferences", :add, c) }

# Transfer to another agent
skill.play(crdt_name: "preferences", operations: [...])
```

### With Amp Code Collaboration
```ruby
# Track collaborative edits
skill.create("code", :text_crdt, "editor-1")
skill.mutate("code", :insert, 0, "def hello")

# Other editors can merge their changes
skill.merge("code-1", "code-2")
```

## Files

| File | Purpose |
|------|---------|
| `lib/crdt_skill.rb` | Main implementation (576 lines) |
| `.ruler/skills/crdt/SKILL.md` | Full documentation |
| `.ruler/skills/crdt/README.md` | This file |

## Integration Points

- **LearnablePLRNetwork**: Track color preference votes with PNCounter
- **ColorHarmonyState**: Use ORSet for active colors, TextCRDT for command logs
- **TailscaleFileTransferSkill**: Compose CRDT merging with file transfers
- **HedgesOpenGames**: Full compositional game theory support

## Key Metrics

- **All 5 core CRDT types**: Implemented ✓
- **Property verification**: Idempotence, Commutativity, Associativity ✓
- **Test coverage**: 5 tests, 100% passing ✓
- **Installation**: Amp, Codex, Music-Topos ✓
- **Documentation**: Complete API reference ✓

---

**Status**: ✅ Production Ready
**Version**: 1.0
**Last Updated**: 2025-12-21
