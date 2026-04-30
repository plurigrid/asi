# Pattern Catalog: Open-Vocabulary Renderer + Protocol Architectures

Distilled from a multi-turn deep-read of terminal/UI compositors, GPU pipelines,
and protocol surfaces. Each pattern names an **invariant**, the **shipped
precedents** that embody it, the **source-of-truth file** in each precedent,
and **what it composes with**.

Companion: `INTERACTION_PATTERNS.md` (agent interaction patterns).
Exemplars: `skills/crdt-vterm/SKILL.md`, `skills/crdt-zigger-oneshot/SKILL.md`.

## P1 — Boundary-as-tagged-union

**Invariant:** State at a moment is a closed-by-enum tagged union; sequencing composes by equality at the boundary.

| Project | Source of truth |
|---|---|
| Ghostty | `src/terminal/parse_table.zig` — `State` enum drives `genTable()` |
| Nushell | `crates/nu-protocol/src/value/mod.rs` — `Value` enum + `PipelineData` |
| Warp (closed) | recovered `Boundary` schema in `ai_exchanges` SQLite + JSON envelope |
| Wave Terminal | `BlockRegistry: viewType → ViewModel` |
| Roc + Zig platform | host interface declared as Zig type |

**Composes with:** P2 (the enum drives codegen), P6 (the tag is what the wire carries).

## P2 — Schema-drives-code (comptime/codegen dispatch)

**Invariant:** The protocol/schema definition *is* the source of all parsing, switching, wire codec, and FFI shim. Hand-written dispatch is the anti-pattern.

| Project | Source of truth |
|---|---|
| River | `build.zig` calls `zig-wayland` scanner over `xdg-shell.xml` + `river-window-management-v1.xml` |
| Ghostty | `genTable()` walks `@typeInfo(State).enum.fields`; `types.zig` walks struct fields → JSON |
| Roc | `main.zig` reads Roc-emitted metadata at comptime, generates FFI shims |
| Mach | `Mod(comptime M: type)` builds dispatch struct via `@Type()` |
| Nushell | `Signature` declares input/output types; `serve_plugin()` generates msgpack codec |
| Zellij | `proto/plugin_command.proto` → Protobuf-generated bridge |

**Composes with:** P1 (the enum/schema is the input), P3 (codegen is what makes the boundary cheap).

## P3 — Carve-the-core, expose-the-protocol

**Invariant:** Separate the language/engine from the policy/host. Publish a small protocol surface. Outside parties complete the system.

| Project | Core | Protocol surface |
|---|---|---|
| Ghostty | `libghostty-vt` (C ABI) | `apprt` callbacks + OSC dispatch |
| River | compositor + scene graph | `river-window-management-v1` (external WM) |
| Roc | language runtime | platform host interface |
| Mach | render core + Objects | `mach_module` declarations |
| Nushell | parse + eval engine | plugin protocol over stdio |
| Wave Terminal | xterm.js + React block tree | `wsh` CLI commands |

The minimal viable carve: name the boundary state (P1), name the messages crossing it (P6), publish how to register external participants (P10).

## P4 — Encoded-stream-as-program

**Invariant:** The data stream is the program. The runtime is a small machine that interprets tags. Closed-by-enum vocabularies are the *anti*-pattern.

| Project | The encoded stream |
|---|---|
| Vello | `Encoding { path_tags, path_data, draw_tags, draw_data, transforms, styles }` |
| Sugarloaf / Rio | vertex `(pos, color, uv, layers: vec2<i32>)` with branching shader |
| Roc + Zig | shared-memory layout of Roc values; Zig reads tags directly |
| Wave | `wsh setmeta key=val` updates block content via tagged stream |

The same property that makes the vocabulary open is what makes it parallel-by-construction (P5). GPUI/WebRender/Bevy's pipeline-state-per-primitive are the *anti*-instances.

## P5 — Sort-middle pipeline with indirect dispatch

**Invariant:** Stage 1 ingests the encoding. Stage 2 sorts/bins by structural property (tile / time / type). Stage 3 runs per-bin compute. Stages communicate via GPU buffers; later stages dispatch themselves from earlier-stage outputs.

| Project | Stages |
|---|---|
| Vello | pathtag scan → flatten → bin → tile alloc → path count (indirect) → backdrop → coarse → tiling (indirect) → fine |
| Bevy | extract → mesh preprocess → cull (compute) → multi_draw_indirect |
| Pathfinder 3 D3D11 | bin.cs → propagate.cs → fill.cs |

`path_count_setup` writes to `indirect_count_buf`; `path_count` dispatches itself from that buffer. **The CPU is out of the loop between scene encoding and final pixels.**

## P6 — Typed-wire-as-capability

**Invariant:** Wire format carries (type tag, payload, optional capability/sealer). Receivers verify capability, dispatch on type, decode payload. Type and right-to-act-on-it travel together.

| Project | Wire format |
|---|---|
| Nushell plugin | msgpack `PluginInput / PluginOutput` with `PipelineDataHeader` initiator + `StreamId` chunks |
| Zellij plugin | Protobuf `ProtobufPluginCommand` + permission gates |
| Warp `multi_agent.v1` | gRPC + Protobuf, capability via OAuth device flow |
| OCapN / Syrup | sealed sturdyrefs + typed records |
| Wave `wsh` | JSON IPC with viewType tag |

**Crucial correspondence:** `wsh setmeta` and Nushell's `PipelineDataHeader` are the *same operation* — initiate a typed conduit, hand back a handle, stream chunks into it.

## P7 — Tiered renderer with capability negotiation

**Invariant:** Same scene description, multiple backends, runtime feature detection picks the best. Negotiation is at startup, not per-frame.

| Project | Tiers |
|---|---|
| Slint | Skia → FemtoVG → Software (RP2040 / STM32 line-by-line) |
| Pathfinder | D3D11 (compute) → D3D9 (CPU bin + GPU fill) |
| Notcurses | Kitty graphics → Sixel → Unicode sextant/octant/Braille → ASCII |
| GPUI | Metal (Mac) → wgpu (everything else) |
| Vello | wgpu → CPU fallback |

## P8 — Per-frame arena, explicit lifetime

**Invariant:** Each frame has its own allocator. Frame-surviving state is explicit. Frame-local state is freed by arena reset.

| Project | Arena hook |
|---|---|
| Mach | `glyph_update_buffer.clearRetainingCapacity()` per frame |
| TigerBeetle | static alloc at init; *no* allocator post-init |
| Bevy | per-frame command buffer pools |
| Vello | `Encoding` vec reset at scene start |

## P9 — Pipelined two-thread (sim ‖ render)

**Invariant:** Simulation for frame N+1 runs concurrently with rendering of frame N. Explicit `extract` step copies the snapshot from sim to render world.

| Project | Boundary |
|---|---|
| Bevy | `Main App` ↔ `RenderApp`; `renderer_extract` snapshot |
| Wave Terminal | xterm.js write-loop (frame N) ‖ React render-loop (frame N+1) |

## P10 — Sandboxed plugin via WASM/process + capability protocol

**Invariant:** Untrusted extensions run in a sandbox (WASM, sub-process, OS namespace). Host calls are mediated by typed capabilities. Extensions register via the carved-core's protocol (P3).

| Project | Sandbox + protocol |
|---|---|
| Zellij | `wasmi` runtime + Protobuf bridge + permission gates |
| Nushell | sub-process plugin + msgpack `PluginInput`/`PluginOutput` |
| Warp | `isolation_platform` (Docker + Linux namespaces) for cloud agents |

## P11 — Typed pipeline composition

**Invariant:** Process output is a typed value, not a byte stream. Composition is by type, not by parsing.

| Project | Typed pipeline |
|---|---|
| Nushell | `Value`-valued pipelines, `Signature` per command |
| Roc | `Effect` interpreter with typed effects |
| Wave | typed view-content into typed blocks |
| Lean / Coq tactic state | proof-term carrying type evidence |

## Composition graph

```
                     P1 (Boundary-as-enum)
                    ╱        │        ╲
              P2 (Codegen)   │   P6 (Typed-wire)
                   │         │         │
                   ╰─→ P3 (Carved-core) ←─╯
                       ╱       │       ╲
              P4 (Encoded)  P10 (Sandbox)  P11 (Typed pipeline)
                   │
                   ↓
              P5 (Sort-middle compute)
                   │
                   ↓
              P8 (Per-frame arena) ←→ P9 (Two-thread pipelining)
                   │
                   ↓
              P7 (Tiered backend)
```

P1 and P2 are the foundation — once you have a closed-by-enum boundary state and codegen from the schema, everything else falls out. P3 is the architectural commitment. P4–P11 pile on top.

## Categorical foundation — Cell A's sheaf condition

Underlying P1: state evolution is a Segal sheaf $F : I^{\mathrm{op}} \to D$ on the poset $I$ of closed intervals of session time, valued in $D$ = category of boundary states. Gluing:

$$F([a,b]) \cong F([a,p]) \times_{F([p,p])} F([p,b])$$

(2-Segal / Mayer–Vietoris condition for two-element covers; Dyckerhoff–Kapranov.)

Concretely $F([p,p])$ is:
- OSC 133: `(cwd, exit_code, env_diff, screen_state)`
- Nushell: a fully materialised `PipelineData::Value`
- Wave: the block's `last_modified_at` row in `ai_exchanges`
- Vello: the path-monoid value at position $p$

**Path-invariance** = sheaf condition: $F([a,b])$ does not depend on the chosen split point. A protocol $\Pi$ is *sufficient* iff it permits recovery of $F([p,p])$ for every $p$.

## Quantum extension

Cell A upgrades to $D$ = dagger-compact-closed category of CPTP quantum channels (Abramsky–Coecke 2004). The gluing becomes partial trace + tensor decomposition. P6 (typed-wire-as-capability) is structurally identical to no-cloning: OCapN sealer/unsealer ↔ unitary/measurement ↔ teleportation/decoherence.

## See also

- `skills/crdt-vterm/SKILL.md` — applied as 7-point P1+P2+P3+P5+P6 upgrade
- `skills/crdt-zigger-oneshot/SKILL.md` — 8-point P1+P2+P3+P6+P8 upgrade
- `INTERACTION_PATTERNS.md` — agent-interaction patterns (companion doc)
