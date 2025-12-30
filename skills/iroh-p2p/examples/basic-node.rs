/// Basic Iroh P2P Node Example
///
/// This example demonstrates:
/// - Creating a P2P node
/// - Accessing node services (blobs, docs, gossip)
/// - Graceful shutdown
///
/// Run with: cargo run --example basic-node

use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    println!("🚀 Starting Iroh P2P node...\n");

    // Spawn an Iroh node with all services enabled
    let node = iroh::node::Builder::default()
        .spawn()
        .await?;

    println!("✅ Node started successfully!");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    // Display available services
    println!("\n📦 Services Available:");
    println!("  • Blobs:  Content distribution (KB to TB)");
    println!("  • Docs:   Document sync (CRDT-based)");
    println!("  • Gossip: Message broadcasting");

    println!("\n🔗 Network Services:");
    println!("  • Direct P2P connections via QUIC");
    println!("  • Automatic hole punching (NAT traversal)");
    println!("  • Relay fallback for restricted networks");

    println!("\n💾 Storage:");
    println!("  • In-memory (for this demo)");
    println!("  • Persistent storage via data_dir()");

    println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("\n⏳ Node running... Press Ctrl+C to stop\n");

    // Keep the node running
    tokio::signal::ctrl_c().await?;

    println!("\n👋 Shutting down node gracefully...");
    println!("   Closing connections and syncing state...");

    // Node automatically cleans up when dropped
    drop(node);

    println!("   Done!\n");

    Ok(())
}
