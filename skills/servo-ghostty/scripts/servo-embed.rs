#!/usr/bin/env rust-script
//! Servo-Ghostty Embedding
//!
//! Minimal Servo embedding that connects to ghostty-web WebSocket
//!
//! Usage:
//!   cargo run --bin servo-ghostty-embed
//!
//! ```cargo
//! [dependencies]
//! servo = { git = "https://github.com/servo/servo" }
//! tokio-tungstenite = "0.21"
//! tokio = { version = "1", features = ["full"] }
//! ```

use std::path::PathBuf;
use tokio_tungstenite::{connect_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Servo-Ghostty Terminal Embedding");
    println!("================================\n");

    // Configuration
    let ghostty_ws = "ws://localhost:7070";
    let terminal_html = get_terminal_html_path();
    let width = 1920;
    let height = 1080;

    println!("Config:");
    println!("  ghostty-web: {}", ghostty_ws);
    println!("  HTML file: {:?}", terminal_html);
    println!("  Window: {}x{}\n", width, height);

    // Connect to ghostty-web WebSocket
    println!("Connecting to ghostty-web...");
    let (ws_stream, _) = connect_async(ghostty_ws).await?;
    println!("✓ Connected to ghostty-web\n");

    let (mut write, mut read) = ws_stream.split();

    // Send INIT frame
    let init_frame = create_init_frame(80, 24);
    write.send(Message::Binary(init_frame)).await?;
    println!("✓ Sent INIT frame\n");

    // Spawn Servo (simplified - actual Servo embedding is more complex)
    println!("Launching Servo browser...");
    println!("  HTML: {:?}", terminal_html);

    // In real implementation, would use Servo's embedding API
    // For now, just demonstrate WebSocket protocol handling

    println!("\nWebSocket message loop:");
    while let Some(msg) = read.next().await {
        match msg? {
            Message::Binary(data) => {
                let frame_type = if data.len() >= 5 { data[4] } else { 0 };

                match frame_type {
                    0x01 => println!("  [OUTPUT] VT sequence ({} bytes)", data.len()),
                    0x02 => println!("  [DIRTY_REGION] Update region"),
                    0x04 => println!("  [PING] Keepalive"),
                    0x05 => println!("  [SPATIAL] Window state"),
                    _ => println!("  [UNKNOWN] Type: 0x{:02x}", frame_type),
                }

                // In real implementation:
                // - Parse VT sequences
                // - Update Servo's HTML canvas
                // - Trigger repaint
            }
            Message::Text(text) => {
                println!("  [TEXT] {}", text);
            }
            Message::Close(_) => {
                println!("  [CLOSE] Connection closed");
                break;
            }
            _ => {}
        }
    }

    Ok(())
}

fn get_terminal_html_path() -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("examples");
    path.push("ghostty-terminal.html");
    path
}

fn create_init_frame(width: u16, height: u16) -> Vec<u8> {
    // ghostty-web INIT frame format:
    // [u32 len][u8 type=0x00][u16 width][u16 height][u8 color_depth=24]

    let mut frame = Vec::new();

    // Payload size = 5 bytes (type + width + height + color_depth)
    let len: u32 = 5;
    frame.extend_from_slice(&len.to_le_bytes());

    // Type: INIT (0x00)
    frame.push(0x00);

    // Width (80 columns)
    frame.extend_from_slice(&width.to_le_bytes());

    // Height (24 rows)
    frame.extend_from_slice(&height.to_le_bytes());

    // Color depth: 24-bit true color
    frame.push(24);

    frame
}

// Full Servo embedding (commented - requires servo crate)
/*
use servo::Servo;
use servo::embedder_traits::{EmbedderMsg, EventLoopWaker};
use servo::servo_url::ServoUrl;

fn launch_servo(html_path: PathBuf, width: u32, height: u32) -> Result<(), Box<dyn std::error::Error>> {
    // Create Servo instance
    let mut servo = Servo::new(/* embedder callbacks */);

    // Load HTML
    let url = ServoUrl::from_file_path(&html_path)?;
    servo.load_url(url);

    // Set viewport
    servo.resize((width, height));

    // Event loop
    loop {
        match servo.get_events() {
            EmbedderMsg::Shutdown => break,
            EmbedderMsg::ReadyToPresent => {
                // Composite and present frame
                servo.present();
            }
            _ => {}
        }
    }

    Ok(())
}
*/
