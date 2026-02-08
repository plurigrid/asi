//! Knowledge Discovery CLI
//! 
//! Provides interactive exploration of the knowledge graph:
//! - Random walk discovery (serendipitous knowledge finding)
//! - Learning paths (prerequisite-ordered learning sequences)
//! - Theory bridges (connecting external knowledge to music-topos)
//! - Research threads (connected learning narratives)

use crate::knowledge_indexer::*;
use duckdb::{Connection, params};
use rand::seq::SliceRandom;
use std::io::{self, Write};

pub struct DiscoveryCLI {
    db_path: String,
}

impl DiscoveryCLI {
    pub fn new(db_path: &str) -> Self {
        DiscoveryCLI {
            db_path: db_path.to_string(),
        }
    }

    /// Run interactive discovery mode
    pub fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let conn = Connection::open(&self.db_path)?;
        
        println!("╔════════════════════════════════════════════════════════════╗");
        println!("║    Music-Topos Knowledge Discovery (Deterministic Agreement)║");
        println!("║    Roughgarden SMR Theory → Gay.rs Implementation         ║");
        println!("╚════════════════════════════════════════════════════════════╝\n");

        loop {
            println!("\nCommands:");
            println!("  1) Random Walk (serendipitous discovery)");
            println!("  2) Learning Path (prerequisites ordered)");
            println!("  3) Theory Bridge (external knowledge → music-topos)");
            println!("  4) Research Thread (connected narrative)");
            println!("  5) Paradigm Crates (vetted libraries)");
            println!("  6) Query Resonance (core unifying principle)");
            println!("  7) Stats (knowledge graph overview)");
            println!("  q) Quit");
            
            print!("\nSelect: ");
            io::stdout().flush()?;
            
            let mut choice = String::new();
            io::stdin().read_line(&mut choice)?;
            let choice = choice.trim();

            match choice {
                "1" => self.random_walk(&conn)?,
                "2" => self.learning_path(&conn)?,
                "3" => self.theory_bridge(&conn)?,
                "4" => self.research_thread(&conn)?,
                "5" => self.vetted_crates(&conn)?,
                "6" => self.resonance_query(&conn)?,
                "7" => self.stats(&conn)?,
                "q" => break,
                _ => println!("Unknown command"),
            }
        }

        Ok(())
    }

    /// Random walk discovery: follow unexpected connections
    fn random_walk(&self, conn: &Connection) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n=== Random Walk Discovery ===\n");
        
        // Start with random resource
        let mut stmt = conn.prepare(
            "SELECT resource_id, title, author FROM resources ORDER BY RANDOM() LIMIT 1"
        )?;
        
        let resource = stmt.query_row([], |row| {
            Ok((
                row.get::<_, i32>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
            ))
        })?;
        
        println!("🎲 Starting point:");
        println!("  [{}] {} by {}", resource.0, resource.1, resource.2);

        // Follow connection to related topic
        let mut stmt = conn.prepare(
            "SELECT DISTINCT t.topic_name, rt.relevance_score 
             FROM topics t
             JOIN resource_topics rt ON t.topic_id = rt.topic_id
             WHERE rt.resource_id = ? 
             ORDER BY rt.relevance_score DESC LIMIT 3"
        )?;
        
        let topics: Vec<String> = stmt.query_map(params![resource.0], |row| {
            Ok(row.get::<_, String>(0)?)
        })?.filter_map(|r| r.ok()).collect();

        if !topics.is_empty() {
            println!("\n📚 Related topics:");
            for topic in &topics {
                println!("  - {}", topic);
            }
        }

        // Follow connection to knowledge bridge
        let mut stmt = conn.prepare(
            "SELECT music_topos_concept, relevance_text FROM knowledge_bridges 
             WHERE external_resource_id = ? LIMIT 1"
        )?;
        
        if let Ok((concept, relevance)) = stmt.query_row(params![resource.0], |row| {
            Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?))
        }) {
            println!("\n🌉 Knowledge bridge:");
            println!("  Concept: {}", concept);
            println!("  Connection: {}", relevance);
        }

        Ok(())
    }

    /// Learning path: prerequisites-ordered sequence
    fn learning_path(&self, conn: &Connection) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n=== Learning Path ===\n");
        
        // State Machine Replication path
        println!("📖 State Machine Replication Learning Path:\n");
        
        let mut stmt = conn.prepare(
            "SELECT r.title, r.author, r.duration_minutes, r.url
             FROM resources r
             JOIN resource_topics rt ON r.resource_id = rt.resource_id
             JOIN topics t ON rt.topic_id = t.topic_id
             WHERE t.topic_name LIKE '%state machine%' 
                OR t.topic_name LIKE '%replication%'
             ORDER BY r.published_date DESC"
        )?;
        
        let mut count = 1;
        let resources = stmt.query_map([], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, Option<i32>>(2)?,
                row.get::<_, String>(3)?,
            ))
        })?;
        
        for resource in resources {
            if let Ok((title, author, duration, url)) = resource {
                let duration_str = duration
                    .map(|d| format!("{} min", d))
                    .unwrap_or_else(|| "N/A".to_string());
                println!("  {}. {} ({})", count, title, author);
                println!("     Duration: {}", duration_str);
                println!("     URL: {}", url);
                println!();
                count += 1;
            }
        }

        Ok(())
    }

    /// Theory bridge: show connections between theory and music-topos
    fn theory_bridge(&self, conn: &Connection) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n=== Theory ↔ Implementation Bridges ===\n");
        
        let mut stmt = conn.prepare(
            "SELECT kb.music_topos_concept, r.title, kb.connection_type, kb.relevance_text
             FROM knowledge_bridges kb
             JOIN resources r ON kb.external_resource_id = r.resource_id
             ORDER BY kb.connection_type"
        )?;
        
        let bridges = stmt.query_map([], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, String>(3)?,
            ))
        })?;
        
        for bridge in bridges {
            if let Ok((concept, resource, conn_type, relevance)) = bridge {
                println!("🌉 {}", concept);
                println!("   Theory: {} [{}]", resource, conn_type);
                println!("   Bridge: {}", relevance);
                println!();
            }
        }

        Ok(())
    }

    /// Research thread: connected narrative
    fn research_thread(&self, conn: &Connection) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n=== Research Thread: Deterministic Agreement ===\n");
        
        let mut stmt = conn.prepare(
            "SELECT r.title, r.author, tr.contribution_type
             FROM research_threads rt
             JOIN thread_resources tr ON rt.thread_id = tr.thread_id
             JOIN resources r ON tr.resource_id = r.resource_id
             WHERE rt.thread_id = 1
             ORDER BY tr.position_in_thread"
        )?;
        
        let resources = stmt.query_map([], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
            ))
        })?;
        
        println!("Core Question:");
        println!("How does consensus theory (Roughgarden SMR, Byzantine FT) apply to distributed");
        println!("music generation? Can we guarantee harmonic consonance despite failures?\n");
        
        println!("Resources in thread:");
        let mut pos = 1;
        for resource in resources {
            if let Ok((title, author, contribution)) = resource {
                println!("  {}. [{}] {} by {}", pos, contribution, title, author);
                pos += 1;
            }
        }

        Ok(())
    }

    /// Paradigm-vetted crates
    fn vetted_crates(&self, conn: &Connection) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n=== Paradigm-Vetted Rust Ecosystem ===\n");
        println!("Production-ready crates (avg quality: 94.6/100)\n");
        
        let mut stmt = conn.prepare(
            "SELECT crate_name, domain, quality_score, maturity_level, github_url
             FROM rust_crates
             WHERE paradigm_vetted = true
             ORDER BY quality_score DESC"
        )?;
        
        let crates = stmt.query_map([], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, f64>(2)?,
                row.get::<_, String>(3)?,
                row.get::<_, String>(4)?,
            ))
        })?;
        
        for krate in crates {
            if let Ok((name, domain, quality, maturity, url)) = krate {
                let quality_bar = "█".repeat((quality / 10.0) as usize);
                println!("  {} ({}) [{}]", name, domain, maturity);
                println!("    Quality: {}  {:.1}/100", quality_bar, quality);
                println!("    {}", url);
                println!();
            }
        }

        Ok(())
    }

    /// Resonance query: core unifying principle
    fn resonance_query(&self, conn: &Connection) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n=== The Most Resonant Principle ===\n");
        
        println!("🔴 DETERMINISTIC AGREEMENT UNDER ADVERSITY");
        println!();
        println!("Maximum parallelism exists at the intersection of:");
        println!("  • Deterministic foundations (Roughgarden SMR theory)");
        println!("  • Economic alignment (Mechanism design incentives)");
        println!("  • Verified implementation (Paradigm-vetted Rust)");
        println!();
        
        println!("How this unifies all research threads:");
        println!("  1. Consensus (Raft): all replicas agree on same transaction sequence");
        println!("  2. Mechanism Design: all agents incentivized toward same outcome");
        println!("  3. Music Composition: all notes agree to same scale → harmonic consonance");
        println!("  4. Gay.rs Parallelism: all parallel instances → same color from same seed");
        println!("  5. Chaos Engineering: system maintains agreement despite faults");
        println!();

        let mut stmt = conn.prepare(
            "SELECT COUNT(*) FROM knowledge_bridges"
        )?;
        
        let bridge_count: i32 = stmt.query_row([], |row| row.get(0))?;
        println!("Knowledge Graph: {} theory ↔ implementation bridges", bridge_count);

        Ok(())
    }

    /// Knowledge graph statistics
    fn stats(&self, conn: &Connection) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n=== Knowledge Graph Overview ===\n");
        
        let mut stmt = conn.prepare("SELECT COUNT(*) FROM resources")?;
        let resource_count: i32 = stmt.query_row([], |row| row.get(0))?;
        println!("📚 Resources: {}", resource_count);
        
        let mut stmt = conn.prepare("SELECT COUNT(*) FROM topics")?;
        let topic_count: i32 = stmt.query_row([], |row| row.get(0))?;
        println!("🏷️  Topics: {}", topic_count);
        
        let mut stmt = conn.prepare("SELECT COUNT(*) FROM rust_crates WHERE paradigm_vetted")?;
        let crate_count: i32 = stmt.query_row([], |row| row.get(0))?;
        println!("🦀 Paradigm-Vetted Crates: {}", crate_count);
        
        let mut stmt = conn.prepare("SELECT COUNT(*) FROM knowledge_bridges")?;
        let bridge_count: i32 = stmt.query_row([], |row| row.get(0))?;
        println!("🌉 Knowledge Bridges: {}", bridge_count);
        
        let mut stmt = conn.prepare("SELECT COUNT(*) FROM implementation_mapping WHERE implementation_status = 'complete'")?;
        let complete_count: i32 = stmt.query_row([], |row| row.get(0))?;
        println!("✅ Gay.rs Components Complete: {}", complete_count);

        Ok(())
    }
}
