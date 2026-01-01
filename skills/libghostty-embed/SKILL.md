---
name: libghostty-embed
description: libghostty terminal embedding for per-vat REPLs with Goblins integration
trit: 1
probe: ls ~/worlds/b/bmorphism/trittty/include/ghostty.h
bundle: terminal
priority: 4
---
# libghostty-embed Skill

**Trit**: +1 (PLUS - terminal output producer)
**Level**: 4 (EXPERT)
**Header**: `~/worlds/b/bmorphism/trittty/include/ghostty.h`

## Core Types

```c
typedef void* ghostty_app_t;
typedef void* ghostty_surface_t;
typedef void* ghostty_config_t;
```

## Per-Vat Terminal

Each Goblins vat gets its own `ghostty_surface_t`:

```zig
pub const VatTerminal = struct {
    surface: c.ghostty_surface_t,
    vat_id: []const u8,
    trit: i8, // GF(3) phase
};
```

## GF(3) Triplet

```
vat-minus (⊖ -1) × vat-zero (⊙ 0) × vat-plus (⊕ +1) = 0 ✓
```

## Canonical Triads

```
move-contract (-1) ⊗ qualia-bank (0) ⊗ libghostty-embed (+1) = 0 ✓
zig-programming (-1) ⊗ nickel (0) ⊗ libghostty-embed (+1) = 0 ✓
```

## Interaction Modes

| Mode | Goblins Syntax | Terminal |
|------|----------------|----------|
| inside_sync | `($ obj 'method)` | Same surface |
| outside_async | `(<- obj 'method)` | Route between surfaces |
| outside_remote | sturdyref | CapTP network |
