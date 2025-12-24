//! MCP Server for Knowledge Discovery
//! 
//! Provides Claude agents with tools to:
//! - Query research resources
//! - Explore learning paths
//! - Discover theory bridges
//! - Find paradigm-vetted crates
//! - Access the resonance principle

use std::process::Command;
use serde_json::{json, Value};

pub struct MCPKnowledgeServer {
    db_path: String,
}

impl MCPKnowledgeServer {
    pub fn new(db_path: &str) -> Self {
        MCPKnowledgeServer {
            db_path: db_path.to_string(),
        }
    }

    /// List available MCP tools for knowledge discovery
    pub fn list_tools(&self) -> Value {
        json!({
            "tools": [
                {
                    "name": "research_resources",
                    "description": "Query research resources by author, type, or topic",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "query": {"type": "string", "description": "Search term (author, topic, or keyword)"},
                            "limit": {"type": "integer", "description": "Max results (default: 10)"}
                        },
                        "required": ["query"]
                    }
                },
                {
                    "name": "learning_path",
                    "description": "Get prerequisites-ordered learning sequence for a topic",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "topic": {"type": "string", "description": "Topic name (e.g., 'State Machine Replication')"}
                        },
                        "required": ["topic"]
                    }
                },
                {
                    "name": "theory_bridges",
                    "description": "Find connections between external theory and music-topos implementation",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "concept": {"type": "string", "description": "Music-topos concept to explore"}
                        }
                    }
                },
                {
                    "name": "paradigm_crates",
                    "description": "Find paradigm-vetted Rust crates by domain",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "domain": {"type": "string", "description": "Domain (e.g., 'async', 'parallelism', 'database')"}
                        }
                    }
                },
                {
                    "name": "resonance_principle",
                    "description": "Query the most resonant principle unifying all research",
                    "inputSchema": {
                        "type": "object",
                        "properties": {}
                    }
                },
                {
                    "name": "research_thread",
                    "description": "Get connected research narrative on deterministic agreement",
                    "inputSchema": {
                        "type": "object",
                        "properties": {}
                    }
                },
                {
                    "name": "knowledge_graph_stats",
                    "description": "Get overview statistics of knowledge graph",
                    "inputSchema": {
                        "type": "object",
                        "properties": {}
                    }
                },
                {
                    "name": "random_walk",
                    "description": "Perform serendipitous knowledge discovery via random walk",
                    "inputSchema": {
                        "type": "object",
                        "properties": {}
                    }
                }
            ]
        })
    }

    /// Execute tool by name
    pub fn execute_tool(&self, tool_name: &str, args: &Value) -> Result<Value, String> {
        match tool_name {
            "research_resources" => self.research_resources(args),
            "learning_path" => self.learning_path(args),
            "theory_bridges" => self.theory_bridges(args),
            "paradigm_crates" => self.paradigm_crates(args),
            "resonance_principle" => self.resonance_principle(),
            "research_thread" => self.research_thread(),
            "knowledge_graph_stats" => self.knowledge_graph_stats(),
            "random_walk" => self.random_walk(),
            _ => Err(format!("Unknown tool: {}", tool_name)),
        }
    }

    fn query_duckdb(&self, sql: &str) -> Result<String, String> {
        let output = Command::new("duckdb")
            .arg(&self.db_path)
            .arg(sql)
            .output()
            .map_err(|e| format!("Failed to execute query: {}", e))?;

        if !output.status.success() {
            return Err(String::from_utf8_lossy(&output.stderr).to_string());
        }

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    fn research_resources(&self, args: &Value) -> Result<Value, String> {
        let query = args["query"]
            .as_str()
            .ok_or("Missing 'query' parameter")?;
        let limit = args["limit"]
            .as_u64()
            .unwrap_or(10);

        let sql = format!(
            "SELECT resource_id, title, author, resource_type, url \
             FROM resources \
             WHERE title ILIKE '%{}%' OR author ILIKE '%{}%' \
             LIMIT {}",
            query.replace("'", "''"), query.replace("'", "''"), limit
        );

        let result = self.query_duckdb(&sql)?;
        Ok(json!({"results": result}))
    }

    fn learning_path(&self, args: &Value) -> Result<Value, String> {
        let topic = args["topic"]
            .as_str()
            .ok_or("Missing 'topic' parameter")?;

        let sql = format!(
            "SELECT r.title, r.author, r.duration_minutes, r.url \
             FROM resources r \
             JOIN resource_topics rt ON r.resource_id = rt.resource_id \
             JOIN topics t ON rt.topic_id = t.topic_id \
             WHERE t.topic_name ILIKE '%{}%' \
             ORDER BY r.published_date DESC",
            topic.replace("'", "''")
        );

        let result = self.query_duckdb(&sql)?;
        Ok(json!({"learning_path": result}))
    }

    fn theory_bridges(&self, args: &Value) -> Result<Value, String> {
        let concept = args["concept"]
            .as_str()
            .ok_or("Missing 'concept' parameter")?;

        let sql = format!(
            "SELECT kb.music_topos_concept, r.title, kb.connection_type, kb.relevance_text \
             FROM knowledge_bridges kb \
             JOIN resources r ON kb.external_resource_id = r.resource_id \
             WHERE kb.music_topos_concept ILIKE '%{}%' \
             ORDER BY kb.connection_type",
            concept.replace("'", "''")
        );

        let result = self.query_duckdb(&sql)?;
        Ok(json!({"theory_bridges": result}))
    }

    fn paradigm_crates(&self, args: &Value) -> Result<Value, String> {
        let domain = args["domain"]
            .as_str()
            .unwrap_or("%");

        let sql = format!(
            "SELECT crate_name, domain, quality_score, maturity_level, github_url \
             FROM rust_crates \
             WHERE paradigm_vetted = true AND domain ILIKE '%{}%' \
             ORDER BY quality_score DESC",
            domain.replace("'", "''")
        );

        let result = self.query_duckdb(&sql)?;
        Ok(json!({"crates": result}))
    }

    fn resonance_principle(&self) -> Result<Value, String> {
        Ok(json!({
            "principle": "Deterministic Agreement Under Adversity",
            "description": "Maximum parallelism exists at intersection of: (1) Deterministic foundations (Roughgarden SMR), (2) Economic alignment (mechanism design incentives), (3) Verified implementation (paradigm-vetted Rust)",
            "unifies": [
                "Consensus (Raft): all replicas agree on same transaction sequence",
                "Mechanism Design: all agents incentivized toward same outcome",
                "Music Composition: all notes agree to same scale → harmony",
                "Gay.rs Parallelism: all parallel instances → same color from seed",
                "Chaos Engineering: system maintains agreement despite faults"
            ]
        }))
    }

    fn research_thread(&self) -> Result<Value, String> {
        let sql = "SELECT r.title, r.author, tr.contribution_type \
                   FROM research_threads rt \
                   JOIN thread_resources tr ON rt.thread_id = tr.thread_id \
                   JOIN resources r ON tr.resource_id = r.resource_id \
                   WHERE rt.thread_id = 1 \
                   ORDER BY tr.position_in_thread";

        let result = self.query_duckdb(sql)?;
        Ok(json!({
            "thread_name": "Deterministic Agreement Under Adversity",
            "core_question": "How does consensus theory apply to distributed music generation?",
            "resources": result
        }))
    }

    fn knowledge_graph_stats(&self) -> Result<Value, String> {
        let stats_queries = vec![
            ("SELECT COUNT(*) as count FROM resources", "resources"),
            ("SELECT COUNT(*) as count FROM topics", "topics"),
            ("SELECT COUNT(*) as count FROM rust_crates WHERE paradigm_vetted", "crates"),
            ("SELECT COUNT(*) as count FROM knowledge_bridges", "bridges"),
            ("SELECT COUNT(*) as count FROM implementation_mapping WHERE implementation_status = 'complete'", "complete_components"),
        ];

        let mut stats = serde_json::Map::new();
        for (sql, key) in stats_queries {
            let result = self.query_duckdb(sql)?;
            // Simple parse of "count" results
            stats.insert(key.to_string(), Value::String(result.trim().to_string()));
        }

        Ok(Value::Object(stats))
    }

    fn random_walk(&self) -> Result<Value, String> {
        let sql = "SELECT resource_id, title, author FROM resources ORDER BY RANDOM() LIMIT 1";
        let resource = self.query_duckdb(sql)?;

        Ok(json!({
            "discovery": "random_walk",
            "resource": resource
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mcp_tools_available() {
        let server = MCPKnowledgeServer::new(":memory:");
        let tools = server.list_tools();
        assert!(tools["tools"].is_array());
        assert!(tools["tools"].as_array().unwrap().len() > 0);
    }
}
