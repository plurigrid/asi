/*!
    Fermyon Serverless CRDT E-Graph Agent Library

    Phase 3C: Deploy distributed agents to Fermyon serverless platform

    Architecture:
    - Each agent runs as independent Fermyon component
    - HTTP endpoints for state queries and operations
    - NATS for inter-agent communication (via Fermyon resources)
    - Spin HTTP trigger for request handling
    - Variable storage for agent state persistence
*/

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use uuid::Uuid;
use chrono::{DateTime, Utc};

// ═══════════════════════════════════════════════════════════════════════════════
// Message Types
// ═══════════════════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
pub enum MessageType {
    SyncRequest,
    SyncResponse,
    StateUpdate,
    Heartbeat,
    Ack,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentMessage {
    pub message_id: String,
    pub msg_type: MessageType,
    pub sender_id: usize,
    pub receiver_id: usize,
    pub timestamp: DateTime<Utc>,
    pub payload: Option<serde_json::Value>,
}

impl AgentMessage {
    pub fn new(
        msg_type: MessageType,
        sender_id: usize,
        receiver_id: usize,
        payload: Option<serde_json::Value>,
    ) -> Self {
        Self {
            message_id: Uuid::new_v4().to_string(),
            msg_type,
            sender_id,
            receiver_id,
            timestamp: Utc::now(),
            payload,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// E-Graph Node
// ═══════════════════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
pub enum Color {
    Red,   // Positive/forward operations
    Blue,  // Negative/backward operations
    Green, // Neutral/identity operations
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ENode {
    pub id: String,
    pub operator: String,
    pub children: Vec<String>,
    pub color: Color,
    pub created_at: DateTime<Utc>,
}

impl ENode {
    pub fn new(operator: String, children: Vec<String>, color: Color) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            operator,
            children,
            color,
            created_at: Utc::now(),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// CRDT E-Graph
// ═══════════════════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CRDTEGraph {
    pub nodes: HashMap<String, ENode>,
    pub node_to_class: HashMap<String, String>,
    pub vector_clock: HashMap<String, u64>,
}

impl CRDTEGraph {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            node_to_class: HashMap::new(),
            vector_clock: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, node: ENode) -> Result<String, String> {
        let node_id = node.id.clone();
        self.nodes.insert(node_id.clone(), node);
        Ok(node_id)
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn increment_clock(&mut self, agent_id: String) {
        let current = self.vector_clock.get(&agent_id).copied().unwrap_or(0);
        self.vector_clock.insert(agent_id, current + 1);
    }
}

impl Default for CRDTEGraph {
    fn default() -> Self {
        Self::new()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Serverless Agent
// ═══════════════════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerlessAgent {
    pub agent_id: usize,
    pub node_id: String,
    pub egraph: CRDTEGraph,
    pub neighbors: Vec<usize>,
    pub messages_received: u64,
    pub messages_sent: u64,
    pub syncs_completed: u64,
    pub created_at: DateTime<Utc>,
}

impl ServerlessAgent {
    pub fn new(agent_id: usize, neighbors: Vec<usize>) -> Self {
        Self {
            agent_id,
            node_id: Uuid::new_v4().to_string(),
            egraph: CRDTEGraph::new(),
            neighbors,
            messages_received: 0,
            messages_sent: 0,
            syncs_completed: 0,
            created_at: Utc::now(),
        }
    }

    pub fn add_node(&mut self, operator: String, color: Color) -> Result<String, String> {
        let node = ENode::new(operator, vec![], color);
        self.egraph.add_node(node)
    }

    pub fn process_message(&mut self, message: &AgentMessage) -> Result<(), String> {
        match message.msg_type {
            MessageType::StateUpdate => {
                self.messages_received += 1;
                self.syncs_completed += 1;
                Ok(())
            }
            _ => {
                self.messages_received += 1;
                Ok(())
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// HTTP Response Types
// ═══════════════════════════════════════════════════════════════════════════════

#[derive(Debug, Serialize, Deserialize)]
pub struct AgentStateResponse {
    pub agent_id: usize,
    pub node_id: String,
    pub egraph_nodes: usize,
    pub neighbors: Vec<usize>,
    pub messages_received: u64,
    pub messages_sent: u64,
    pub syncs_completed: u64,
    pub uptime_seconds: f64,
}

impl From<&ServerlessAgent> for AgentStateResponse {
    fn from(agent: &ServerlessAgent) -> Self {
        let uptime = Utc::now()
            .signed_duration_since(agent.created_at)
            .num_seconds() as f64;

        Self {
            agent_id: agent.agent_id,
            node_id: agent.node_id.clone(),
            egraph_nodes: agent.egraph.node_count(),
            neighbors: agent.neighbors.clone(),
            messages_received: agent.messages_received,
            messages_sent: agent.messages_sent,
            syncs_completed: agent.syncs_completed,
            uptime_seconds: uptime,
        }
    }
}

pub use self::{AgentMessage, Color, CRDTEGraph, ENode, MessageType, ServerlessAgent, AgentStateResponse};


// ═══════════════════════════════════════════════════════════════════════════════
// P0: Core Infrastructure Components
// ═══════════════════════════════════════════════════════════════════════════════

pub mod stream_red;
pub mod stream_blue;
pub mod stream_green;

pub use stream_red::StreamRed;
pub use stream_blue::StreamBlue;
pub use stream_green::StreamGreen;

// ═══════════════════════════════════════════════════════════════════════════════
// P1: Coordination Layer Components
// ═══════════════════════════════════════════════════════════════════════════════

pub mod agent_orchestrator;
pub mod duck_colors;

pub use agent_orchestrator::{OrchestrationState, AgentMetadata, RoundStatistics};
pub use duck_colors::{ColorAssigner, Polarity};
