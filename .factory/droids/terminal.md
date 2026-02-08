---
name: terminal
description: Terminal emulation = libghostty-vt + tmux + zsh + fzf + ripgrep.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# terminal

Terminal emulation and tools powered by libghostty-vt.

## libghostty-vt (Core Terminal Emulation)

> "libghostty-vt is a zero-dependency library that provides an API for parsing
> terminal sequences and maintaining terminal state" — Mitchell Hashimoto

### What is libghostty-vt?

A C-compatible library extracted from Ghostty for embedding terminal emulation:

| Feature | Description |
|---------|-------------|
| Zero dependencies | No libc required |
| SIMD-optimized | Fast parsing of escape sequences |
| Unicode support | Full UTF-8/grapheme handling |
| Memory efficient | Optimized for embedded use |
| Fuzz-tested | Valgrind-verified, production-proven |

### VT Sequence Types

```
┌─────────────────────────────────────────────────────────────┐
│ C0 Control Characters (0x00-0x1F)                           │
│   BEL (0x07) - Bell/alert                                   │
│   BS  (0x08) - Backspace                                    │
│   TAB (0x09) - Horizontal tab                               │
│   LF  (0x0A) - Line feed                                    │
│   CR  (0x0D) - Carriage return                              │
│   ESC (0x1B) - Escape (starts sequences)                    │
├─────────────────────────────────────────────────────────────┤
│ Escape Sequences (ESC + final)                              │
│   ESC 7    - DECSC (save cursor)                            │
│   ESC 8    - DECRC (restore cursor)                         │
│   ESC D    - IND (index/scroll down)                        │
│   ESC M    - RI (reverse index/scroll up)                   │
│   ESC c    - RIS (full reset)                               │
├─────────────────────────────────────────────────────────────┤
│ CSI Sequences (ESC [ params final)                          │
│   CSI n A  - CUU (cursor up n)                              │
│   CSI n B  - CUD (cursor down n)                            │
│   CSI n C  - CUF (cursor forward n)                         │
│   CSI n D  -