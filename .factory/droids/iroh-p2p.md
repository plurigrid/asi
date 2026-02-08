---
name: iroh-p2p
description: Build modern peer-to-peer applications with Iroh. QUIC-based P2P networking, hole punching, content distribution, and decentralized data synchronization.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Iroh P2P Development

Build decentralized, peer-to-peer applications with **Iroh** — a modern Rust P2P library based on QUIC with automatic hole punching, relay fallback, and content distribution.

## What is Iroh?

Iroh is a **nextgen P2P library** that implements:
- 🔗 **Direct P2P connections** via QUIC (UDP-based, faster than TCP)
- 🔄 **Automatic hole punching** (NAT traversal without complexity)
- 📡 **Relay fallback** (works even behind restrictive firewalls)
- 📦 **Content distribution** (iroh-blobs for KB-TB transfers)
- 📝 **Document sync** (iroh-docs for collaborative state)
- 💬 **Gossip protocol** (iroh-gossip for message broadcasting)

**Iroh represents data sovereignty**: users control their own nodes, direct connections replace central servers, and data stays decentralized.

---

## Quick Start Project

### 1. Initialize Iroh Project

```bash
cargo new my_p2p_app
cd my_p2p_app

# Add dependencies
cargo add iroh@0.13
cargo add tokio --features full
cargo add anyhow
cargo add tracing tracing-subscriber
```

### 2. Create a Basic P2P Node

```rust
use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    // Spawn an Iroh node with all services
    let node = iroh::node::Builder::default()
        .spawn()
        .await?;

    println!("✅ P2P node started!");
    println!("  📦 Blobs:  Available");
    println!("  📝 Docs:   Available");
    println!("  💬 Gossip: Available");

    // Keep running
    println!("\n⏳ Running... (Ctrl+C to stop)");
    tokio::signal::ctrl_c().await?;
    println!("👋 Shutting down...");

    Ok(())
}
```

### 3. Build and Run

```bash
cargo build --release
./target/release/my_p2p_app
```

---

## Core Concepts

### Node Identity

Every Iroh node has a **node ID** (public key) that other peers can connect to:

```rust
// Access node ID through services
let node_id = node.blobs.node_id().await?;
println!("My node ID: {}", node_id);

// Share this with other peers to establish connections
```

### Services

Ir