# Cross-Runtime Syrup Exchange Skill

## Overview

This skill enables content-addressed interoperability between three Syrup implementations:
- **Clojure (Babashka)** - `syrup.clj`
- **Rust** - `ocapn-syrup` crate
- **Zig** - `zig-syrup`

All three produce **identical CIDs** for the same data structures, enabling trustless cross-runtime communication.

## Canonical CID

```
06fe1dc709bea744f8a0e1cd767210cd90f2b78200f574497e876c2778fa7ffb
```

This CID represents a skill invocation that is identical across all runtimes:
```
<12"skill:invoke[7'gay-mcp7'palette{1"n4+4"seed1069+}0+]>
```

## Usage

### Run Cross-Runtime Verification

```bash
# Zig
zig build cross-runtime

# Or run the example directly
zig run examples/cross_runtime_exchange.zig
```

### Expected Output

```
╔══════════════════════════════════════════════════════════════════╗
║     Zig (zig-syrup) Cross-Runtime Exchange                        ║
╚══════════════════════════════════════════════════════════════════╝

=== Zig Encoding & CID Computation ===

skill-invocation     CID: 06fe1dc7...78fa7ffb [57 bytes]
                     ✓ MATCHES CANONICAL CID

=== Cross-Runtime Compatibility ===

All CIDs match between:
  • Clojure (Babashka) - syrup.clj
  • Rust - ocapn-syrup crate
  • Zig - zig-syrup

Canonical skill:invoke CID:
  06fe1dc709bea744f8a0e1cd767210cd90f2b78200f574497e876c2778fa7ffb
```

## Key Compatibility Rules

1. **Record labels must be Strings** (not Symbols)
   - ✅ `"skill:invoke"` (string)
   - ❌ `'skill:invoke` (symbol)

2. **Record fields must be wrapped in a Sequence/List**
   - ✅ `[7'gay-mcp7'palette{...}0+]` (list)
   - ❌ `7'gay-mcp7'palette{...}0+` (bare)

3. **Dictionary keys must be Strings** for canonical ordering
   - ✅ `{"n" 4 "seed" 1069}` (string keys)
   - ❌ `{n 4 seed 1069}` (symbol keys)

## Cross-Runtime Use Cases

### 1. Content-Addressed Skill Invocation
```
Client (Clojure) → Router (Rust) → Worker (Zig)
     │                  │               │
     └──── Same CID ────┴───────┬───────┘
                                ↓
                    Content-Addressed Cache
```

### 2. Embedded-to-Cloud Communication
```
Sensor Device (Zig) → Gateway (Rust) → Analytics (Clojure)
        │                  │                  │
        └────── Same CID representing sensor reading ──────┘
```

### 3. Trustless Data Verification
```
Producer signs CID → Network transmits bytes → Consumer verifies CID
       │                                            │
       └──────────── Cryptographic guarantee ───────┘
```

## Files

- `examples/cross_runtime_exchange.zig` - Zig implementation
- `examples/cross_runtime_exchange.rs` - Rust implementation
- `syrup_cross_runtime_exchange.clj` - Clojure implementation
- `SYRUP_CROSS_RUNTIME_EXCHANGE.md` - Full documentation

## Related Skills

- `bandwidth-benchmark` - Measure throughput across runtimes
