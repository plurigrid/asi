---
name: lazyjj
description: lazyjj — Ratatui TUI for Jujutsu (jj) with interactive log, files, bookmarks, and diff panels
version: 1.0.0
trit: 0
role: ERGODIC
color: "#7B5EA7"
source: brew install lazyjj
---

# lazyjj

Interactive TUI for Jujutsu/jj. Built in Rust with Ratatui. Wraps `jj` CLI.

**Trit**: 0 (ERGODIC) — Coordinator role: visual interface mediating between jj operations and user intent

---

## Overview

lazyjj presents jj repository state as interactive panels — log, files, bookmarks — with keyboard-driven commands for all common operations. Think lazygit but for jj.

- **Log tab** — scroll commit graph, view diffs in side panel
- **Files tab** — current change's files with inline diff
- **Bookmarks tab** — manage bookmarks with track/untrack/rename
- **Conflicts** — view and navigate conflict markers
- **Mouse support** — clickable panels

---

## Installation

```bash
# macOS (Homebrew)
brew install lazyjj

# Cargo
cargo install lazyjj

# From source
git clone https://github.com/Cretezy/lazyjj
cd lazyjj && cargo install --path .
```

Requires `jj` CLI installed and on PATH.

---

## Usage

```bash
# Launch in current repo
lazyjj

# Specify repo path
lazyjj -p /path/to/repo
```

---

## Keybindings

### Global

| Key | Action |
|-----|--------|
| `1` / `2` / `3` | Switch to Log / Files / Bookmarks tab |
| `q` / `Esc` | Back / Quit |
| `?` | Help |
| `j` / `k` or `↓` / `↑` | Navigate |
| `Enter` | Select / Expand |

### Log Tab

| Key | Action |
|-----|--------|
| `n` | New change from selected |
| `e` / `E` | Edit selected change |
| `d` | Describe (set commit message) |
| `a` | Abandon change |
| `s` / `S` | Squash into selected |
| `b` | Set bookmark on selected |
| `r` | Change revset filter |
| `f` | Git fetch |
| `p` | Git push |
| `w` | Toggle color-word / git diff |
| `Enter` | View files of selected change |

### Files Tab

| Key | Action |
|-----|--------|
| `w` | Toggle color-word / git diff |
| `Enter` | View file diff |

### Bookmarks Tab

| Key | Action |
|-----|--------|
| `c` | Create bookmark |
| `r` | Rename bookmark |
| `d` | Delete bookmark |
| `t` | Track remote bookmark |
| `u` | Untrack bookmark |
| `f` | Forget bookmark |
| `n` | New change from bookmarked change |

---

## Workflow Examples

### Quick Review & Squash

```
lazyjj
  → Log tab: scroll to fixup commit
  → s to squash into parent
  → d to update description
  → p to push
```

### Interactive Rebase-like Flow

```
lazyjj
  → Log tab: navigate to change
  → e to edit (jj edit)
  → make changes in editor
  → return to lazyjj
  → changes auto-snapshotted
```

### Bookmark Management

```
lazyjj
  → 3 for Bookmarks tab
  → c to create, type name
  → f to fetch latest
  → t to track remote bookmark
```

---

## Configuration

lazyjj reads jj's config. Custom diff tool:

```toml
# ~/.config/jj/config.toml
[ui]
diff.tool = ["delta", "--side-by-side"]
```

---

## Triadic Composition

```
lazyjj (0)  +  jj (+1)  +  pijul (-1)  = 0 ✓
Coordinator    Generator    Validator
```

lazyjj coordinates user interaction, jj generates changes, pijul validates patch-theoretic soundness.

---

## References

- [lazyjj on GitHub](https://github.com/Cretezy/lazyjj) (970+ ★)
- [lazyjj on Homebrew](https://formulae.brew.sh/formula/lazyjj)
- [lazyjj on crates.io](https://lib.rs/crates/lazyjj)
- [Ratatui](https://ratatui.rs/) — TUI framework
- [jj skill](../jj/SKILL.md)
- [pijul skill](../pijul/SKILL.md)
