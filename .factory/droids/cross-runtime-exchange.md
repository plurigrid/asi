---
name: cross-runtime-exchange
description: "Content-addressed interoperability between Clojure, Rust, and Zig Syrup implementations with identical CIDs"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

Cross-Runtime Syrup Exchange skill enabling content-addressed interoperability between three Syrup implementations: Clojure (Babashka), Rust (ocapn-syrup), and Zig (zig-syrup). All three produce identical CIDs for the same data structures, enabling trustless cross-runtime communication.

Use when:
- Testing cross-runtime Syrup compatibility
- Verifying CID consistency across implementations
- Building interoperable OCapN systems
