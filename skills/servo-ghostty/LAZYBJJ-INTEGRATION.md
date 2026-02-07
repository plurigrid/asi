# Servo-Ghostty + Lazybjj Integration

**Version control UI in web terminal tiles with GF(3) coloring**

---

## Overview

Integration between:
1. **servo-ghostty**: Web terminal with CSS Color Level 4
2. **lazybjj**: TUI for jj with Gay.jl GF(3) coloring (Rust)
3. **lazybjj-unison**: Unison types for GF(3) + RGB (local)

---

## Architecture

```
Servo Browser (CSS Grid tiles)
    ↓
Tile 1: lazybjj TUI (jj version control)
    ├─ Commit graph with GF(3) colors
    ├─ Plus (+1): New features (green)
    ├─ Ergodic (0): Refactors (yellow)
    └─ Minus (-1): Bug fixes (red)
    ↓
Tile 2: Terminal (shell)
    ↓
Tile 3: File editor
    ↓
Tile 4: Test output
    ↓
ghostty-web WebSocket :7070
    ↓
Ghostty Native
```

---

## Component Details

### 1. Lazybjj (Rust TUI)

**Repository**: https://github.com/plurigrid/lazybjj
**Language**: Rust (277,521 bytes)
**Description**: "TUI for jj with Gay.jl GF(3) coloring - Brazilian Jiu-jitsu for version control"

**Key Features**:
- jj (Jujutsu) version control TUI
- Gay.jl deterministic coloring
- GF(3) trit classification for commits
- Golden ratio (φ) or Plastic constant (φ₂) color spacing

**Commit Classification**:
```rust
enum CommitType {
    Feature,    // +1 (Plus) - Generates new functionality
    Refactor,   // 0 (Ergodic) - Maintains equilibrium
    Bugfix,     // -1 (Minus) - Validates/corrects
}

fn classify_commit(message: &str) -> Trit {
    if message.starts_with("feat:") || message.starts_with("add:") {
        Trit::Plus
    } else if message.starts_with("fix:") || message.starts_with("remove:") {
        Trit::Minus
    } else {
        Trit::Ergodic
    }
}
```

**Color Assignment**:
```rust
fn commit_color(index: usize, trit: Trit) -> Rgb {
    // Plastic constant spiral (φ₂ = 1.3247...)
    let hue = (index as f32 * PHI2 * 360.0) % 360.0;

    let lightness = match trit {
        Trit::Plus => 0.6,      // Brighter (generating)
        Trit::Ergodic => 0.5,   // Medium (maintaining)
        Trit::Minus => 0.4,     // Darker (correcting)
    };

    Hsl::new(hue, 0.7, lightness).to_rgb()
}
```

### 2. Lazybjj-Unison (Local Types)

**Location**: `/Users/bob/i/lazybjj-unison/bjj/`
**Language**: Unison
**Status**: Phase 1 Complete ✓

**Files** (6 files, ~500 LOC):
- `constants.u`: φ, φ₂, ZUBUYUL_SEED (1069)
- `trit.u`: GF(3) types and operations
- `rgb.u`: RGB/HSL conversions
- `plastic.u`: Plastic constant sequence
- `splitmix.u`: SplitMix64 PRNG
- `test.u`: Test suite

**Key Types**:
```unison
structural type Trit = Minus | Ergodic | Plus

structural type Rgb = { r : Float, g : Float, b : Float }
structural type Hsl = { h : Float, s : Float, l : Float }

PHI2 : Float
PHI2 = 1.3247179572447... -- Plastic constant

ZUBUYUL_SEED : Nat
ZUBUYUL_SEED = 1069
```

### 3. Servo-Ghostty Terminal

**Location**: `/Users/bob/i/asi/skills/servo-ghostty/`
**Language**: HTML/CSS/JavaScript + Rust
**Status**: Ready for implementation ✓

**Integration Point**:
- Run lazybjj in Servo terminal tile
- CSS Color Level 4 for GF(3) colors
- Oklch color space (perceptual uniformity)

---

## Integration Implementation

### Phase 1: Lazybjj in Terminal Tile

**HTML** (`examples/lazybjj-tile.html`):
```html
<div class="tile-grid">
  <!-- Tile 1: Lazybjj -->
  <div class="tile lazybjj" id="tile1">
    <div class="tile-header">
      <span>Version Control (jj)</span>
      <span class="gf3-indicator">GF(3): Balanced</span>
    </div>
    <canvas id="lazybjj-canvas"></canvas>
  </div>

  <!-- Tile 2: Shell -->
  <div class="tile shell" id="tile2">
    <canvas id="shell-canvas"></canvas>
  </div>
</div>
```

**CSS** (GF(3) colors):
```css
/* GF(3) commit colors (Oklch perceptual) */
.commit-plus {
  /* +1 Generator - New features */
  background: oklch(60% 0.15 140);  /* Green */
  border-left: 4px solid oklch(55% 0.18 140);
}

.commit-ergodic {
  /* 0 Ergodic - Refactors */
  background: oklch(65% 0.12 80);   /* Yellow */
  border-left: 4px solid oklch(60% 0.15 80);
}

.commit-minus {
  /* -1 Validator - Bug fixes */
  background: oklch(55% 0.18 20);   /* Red */
  border-left: 4px solid oklch(50% 0.20 20);
}

/* Plastic constant hue rotation */
.commit-0  { filter: hue-rotate(0deg); }
.commit-1  { filter: hue-rotate(132deg); }   /* φ₂ * 360° ≈ 132° */
.commit-2  { filter: hue-rotate(264deg); }
.commit-3  { filter: hue-rotate(36deg); }    /* (3 * 132) % 360 */
```

**JavaScript** (Launch lazybjj):
```javascript
async function launchLazybjj(tileId) {
  const canvas = document.getElementById(`${tileId}-canvas`);
  const ctx = canvas.getContext('2d');

  // Send command to ghostty-web to launch lazybjj
  const command = {
    type: 'EXECUTE',
    cmd: 'lazybjj',
    cwd: '/Users/bob/i/asi'
  };

  await sendWebSocketCommand(command);

  // Render lazybjj output with GF(3) colors
  ws.onmessage = (event) => {
    const frame = parseFrame(event.data);

    if (frame.type === 'OUTPUT') {
      renderLazybjjOutput(ctx, frame.data);
    }
  };
}

function renderLazybjjOutput(ctx, data) {
  // Parse jj log output
  const commits = parseJjLog(data);

  commits.forEach((commit, i) => {
    const y = i * 24;

    // Classify commit by message
    const trit = classifyCommit(commit.message);

    // Get plastic constant color
    const color = getPlasticColor(i, trit);

    // Render commit line
    ctx.fillStyle = color;
    ctx.fillText(commit.hash.slice(0, 8), 10, y);
    ctx.fillText(commit.message, 100, y);
  });
}

function classifyCommit(message) {
  if (/^(feat|add|new):/.test(message)) return 'plus';
  if (/^(fix|remove|delete):/.test(message)) return 'minus';
  return 'ergodic';
}

function getPlasticColor(index, trit) {
  // Plastic constant spiral
  const PHI2 = 1.3247179572447;
  const hue = (index * PHI2 * 360) % 360;

  const lightness = {
    'plus': 60,
    'ergodic': 65,
    'minus': 55
  }[trit];

  return `oklch(${lightness}% 0.15 ${hue})`;
}
```

### Phase 2: Unison Type Integration

**Bridge Unison ↔ JavaScript**:
```javascript
// Load Unison types via WebAssembly (future)
import { Trit, Rgb, PHI2, ZUBUYUL_SEED } from './bjj-unison.wasm';

function classifyCommitUnison(message) {
  // Use Unison Trit type
  return Trit.fromCommitMessage(message);
}

function getColorUnison(index, trit) {
  // Use Unison Rgb type
  return Rgb.fromPlasticSequence(index, trit, PHI2);
}
```

### Phase 3: GF(3) Conservation Dashboard

**HTML**:
```html
<div class="gf3-dashboard">
  <h3>Repository GF(3) Balance</h3>

  <div class="gf3-stats">
    <div class="stat plus">
      <span class="label">Features (+1)</span>
      <span class="value" id="count-plus">42</span>
    </div>

    <div class="stat ergodic">
      <span class="label">Refactors (0)</span>
      <span class="value" id="count-ergodic">38</span>
    </div>

    <div class="stat minus">
      <span class="label">Fixes (-1)</span>
      <span class="value" id="count-minus">40</span>
    </div>
  </div>

  <div class="gf3-conservation">
    <span>Sum: 42 + 0 + (-40) = 2 ≡ -1 (mod 3)</span>
    <span class="status warning">⚠ Not conserved</span>
  </div>

  <div class="gf3-recommendation">
    <p>Need 1 more Minus (-1) commit to balance</p>
    <button onclick="suggestBalancingCommit()">
      Suggest fix
    </button>
  </div>
</div>
```

**JavaScript**:
```javascript
function analyzeRepositoryBalance() {
  const commits = getCommitHistory();

  let counts = { plus: 0, ergodic: 0, minus: 0 };

  commits.forEach(commit => {
    const trit = classifyCommit(commit.message);
    counts[trit]++;
  });

  const sum = counts.plus - counts.minus;
  const mod3 = ((sum % 3) + 3) % 3;

  return {
    counts,
    sum,
    mod3,
    conserved: mod3 === 0
  };
}

function suggestBalancingCommit() {
  const balance = analyzeRepositoryBalance();

  if (balance.conserved) {
    console.log("✓ Repository is GF(3) conserved");
    return;
  }

  const needed = (3 - balance.mod3) % 3;

  const suggestions = {
    1: "Create a feature (+1) to balance",
    2: "Ergodic commit (0) won't help. Need +1 or -1.",
    0: "Create a bugfix (-1) to balance"
  }[needed];

  console.log(`Suggestion: ${suggestions}`);
}
```

---

## Use Cases

### Use Case 1: Version Control in Tile

```bash
# 1. Start Servo terminal
~/i/asi/skills/servo-ghostty/scripts/run-terminal.sh

# 2. In Tile 1: Launch lazybjj
> lazybjj

# 3. See commit graph with GF(3) colors:
#    Green (+1): feat: Add Servo integration
#    Yellow (0): refactor: Clean up types
#    Red (-1): fix: Color conversion bug

# 4. Navigate with jj commands
> jj log
> jj diff
> jj describe
```

### Use Case 2: GF(3) Balanced Development

```bash
# 1. Check repository balance
> jj log | grep -E "^(feat|fix|refactor):" | ./analyze-gf3.sh

# Output:
# Plus (+1): 15 commits
# Ergodic (0): 12 commits
# Minus (-1): 13 commits
# Sum: 15 + 0 - 13 = 2 ≡ -1 (mod 3)
# ⚠ Not conserved - need 1 Minus (-1) commit

# 2. Create balancing commit
> jj describe -m "fix: Balance GF(3) conservation"

# 3. Verify
# Sum: 15 + 0 - 14 = 1 ≡ +1 (mod 3)
# Still not balanced!

# Need 2 more Minus commits OR 1 Plus commit
```

### Use Case 3: Plastic Constant Color Sequence

```bash
# In lazybjj, commits are colored by plastic constant:
# Commit 0: Hue 0°
# Commit 1: Hue 132° (φ₂ * 360° = 476.5° ≡ 116.5°)
# Commit 2: Hue 264°
# Commit 3: Hue 36°
# ...

# Low-discrepancy sequence for visual separation
```

---

## File Structure

```
asi/skills/servo-ghostty/
├── SKILL.md
├── README.md
├── LAZYBJJ-INTEGRATION.md         # This file
├── scripts/
│   ├── servo-embed.rs
│   ├── run-terminal.sh
│   └── lazybjj-tile.js            # NEW
├── examples/
│   ├── ghostty-terminal.html
│   ├── lazybjj-tile.html          # NEW
│   └── gf3-dashboard.html         # NEW
└── references/
    ├── lazybjj-rust.md            # NEW
    ├── lazybjj-unison.md          # NEW
    └── plastic-constant.md        # NEW
```

---

## Dependencies

### Runtime
- Servo browser engine
- ghostty-web WebSocket server
- lazybjj (Rust TUI)
- jj (Jujutsu version control)

### Development
- Unison (for type definitions)
- Rust (for lazybjj)
- Zig (for ghostty-web)

---

## Contribution Roadmap

### Week 1: Setup
- [x] Create servo-ghostty skill structure
- [x] Document lazybjj integration
- [ ] Fork lazybjj for Servo integration
- [ ] Test jj with GF(3) commit classification

### Week 2: Integration
- [ ] Implement lazybjj-tile.html
- [ ] Add GF(3) dashboard
- [ ] Connect to ghostty-web
- [ ] Plastic constant coloring

### Week 3: Unison Bridge
- [ ] Compile Unison to WASM
- [ ] Load bjj types in JavaScript
- [ ] Use Unison Trit/Rgb types
- [ ] Test conservation checking

### Week 4: Polish
- [ ] Documentation
- [ ] Examples
- [ ] Tests
- [ ] PR to plurigrid/asi

---

## GF(3) Conservation in Version Control

### Theorem: Balanced Repository

```
For a repository to be GF(3) conserved:

Σ (Features + Refactors - Bugfixes) ≡ 0 (mod 3)

Where:
  Features = +1 (Plus) commits
  Refactors = 0 (Ergodic) commits
  Bugfixes = -1 (Minus) commits
```

### Example Repository

```
Initial:
  feat: Add login (Plus +1)
  feat: Add logout (Plus +1)
  fix: Login bug (Minus -1)

Sum: +1 + 1 - 1 = +1 ≡ +1 (mod 3) ⚠ NOT CONSERVED

Add balancing commits:
  refactor: Extract auth module (Ergodic 0)
  fix: Logout bug (Minus -1)
  fix: Session bug (Minus -1)

Sum: +1 + 1 + 0 - 1 - 1 - 1 = -1 ≡ -1 (mod 3) ⚠ STILL NOT CONSERVED

Add final balancing:
  feat: Add password reset (Plus +1)

Sum: +1 + 1 + 1 + 0 - 1 - 1 - 1 = 0 ≡ 0 (mod 3) ✓ CONSERVED
```

---

## Integration with Hatchery

### Hatchery SSH Access

```bash
# Connect to hatchery (remote Julia)
ssh hatchery

# Check for lazybjj or jj
which jj
which lazybjj

# If not installed:
# Install jj
cargo install jj-cli

# Clone and build lazybjj
git clone https://github.com/plurigrid/lazybjj
cd lazybjj
cargo build --release
```

### Remote Lazybjj Session

```bash
# Local: Forward Servo terminal to hatchery
ssh -L 7070:localhost:7070 hatchery

# Hatchery: Run ghostty-web
ghostty-web &

# Local: Connect Servo
servo examples/lazybjj-tile.html
# → Shows hatchery jj repositories
```

---

## Next Steps

1. **Push to plurigrid/asi**:
   ```bash
   cd ~/i/asi
   git checkout -b servo-ghostty-skill
   git add skills/servo-ghostty/
   git commit -m "feat: Add Servo-Ghostty skill with lazybjj integration"
   git push origin servo-ghostty-skill
   gh pr create --title "Servo-Ghostty skill + lazybjj integration"
   ```

2. **Test with lazybjj**:
   ```bash
   # Build lazybjj locally
   git clone https://github.com/plurigrid/lazybjj
   cd lazybjj
   cargo build --release

   # Run in Servo terminal
   ~/i/asi/skills/servo-ghostty/scripts/run-terminal.sh
   # → Launch lazybjj in tile
   ```

3. **Hatchery integration**:
   ```bash
   # Test remote access
   ssh hatchery "which jj"
   # → Install if needed
   ```

**Status**: Ready to contribute to plurigrid/asi ✓

**Ω**
