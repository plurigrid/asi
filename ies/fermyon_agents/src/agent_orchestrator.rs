/*!
    agent-orchestrator: Lifecycle & Synchronization Coordination

    P1 Component: Manages agent lifecycle, coordinates synchronization rounds,
    orchestrates message routing across distributed network.

    Responsibilities:
    - Agent initialization and registration
    - Synchronization round scheduling
    - Network topology management
    - Message routing and delivery coordination
    - Health monitoring and recovery
*/

use crate::{ServerlessAgent, AgentMessage, MessageType};
use std::collections::{HashMap, VecDeque};
use chrono::{DateTime, Utc, Duration};

/// Network orchestration state
#[derive(Debug, Clone)]
pub struct OrchestrationState {
    pub agents: HashMap<usize, AgentMetadata>,
    pub topology: HashMap<usize, Vec<usize>>,
    pub sync_schedule: VecDeque<usize>,
    pub current_round: u64,
    pub round_start: DateTime<Utc>,
}

/// Agent metadata for orchestration
#[derive(Debug, Clone)]
pub struct AgentMetadata {
    pub agent_id: usize,
    pub is_active: bool,
    pub last_heartbeat: DateTime<Utc>,
    pub syncs_completed: u64,
    pub messages_processed: u64,
    pub health_score: f64,
}

impl OrchestrationState {
    pub fn new() -> Self {
        Self {
            agents: HashMap::new(),
            topology: HashMap::new(),
            sync_schedule: VecDeque::new(),
            current_round: 0,
            round_start: Utc::now(),
        }
    }

    /// Register agent with orchestrator
    pub fn register_agent(&mut self, agent_id: usize, neighbors: Vec<usize>) -> Result<(), String> {
        if self.agents.contains_key(&agent_id) {
            return Err(format!("Agent {} already registered", agent_id));
        }

        self.agents.insert(
            agent_id,
            AgentMetadata {
                agent_id,
                is_active: true,
                last_heartbeat: Utc::now(),
                syncs_completed: 0,
                messages_processed: 0,
                health_score: 1.0,
            },
        );

        self.topology.insert(agent_id, neighbors);
        self.sync_schedule.push_back(agent_id);

        Ok(())
    }

    /// Deregister agent
    pub fn deregister_agent(&mut self, agent_id: usize) -> Result<(), String> {
        if !self.agents.contains_key(&agent_id) {
            return Err(format!("Agent {} not found", agent_id));
        }

        self.agents.remove(&agent_id);
        self.topology.remove(&agent_id);
        self.sync_schedule.retain(|id| *id != agent_id);

        Ok(())
    }

    /// Update agent heartbeat
    pub fn update_heartbeat(&mut self, agent_id: usize) -> Result<(), String> {
        if let Some(metadata) = self.agents.get_mut(&agent_id) {
            metadata.last_heartbeat = Utc::now();
            Ok(())
        } else {
            Err(format!("Agent {} not found", agent_id))
        }
    }

    /// Check agent health
    pub fn check_agent_health(&mut self, timeout_seconds: i64) -> Result<(), String> {
        let now = Utc::now();
        let timeout = Duration::seconds(timeout_seconds);

        for metadata in self.agents.values_mut() {
            let elapsed = now.signed_duration_since(metadata.last_heartbeat);

            if elapsed > timeout {
                metadata.is_active = false;
                metadata.health_score = 0.0;
            } else {
                metadata.is_active = true;
                let health = 1.0 - (elapsed.num_seconds() as f64 / timeout_seconds as f64);
                metadata.health_score = health.max(0.0).min(1.0);
            }
        }

        Ok(())
    }

    /// Get active agents
    pub fn get_active_agents(&self) -> Vec<usize> {
        self.agents
            .values()
            .filter(|m| m.is_active)
            .map(|m| m.agent_id)
            .collect()
    }

    /// Get network diameter
    pub fn get_network_diameter(&self) -> Option<usize> {
        if self.topology.is_empty() {
            return None;
        }

        let mut max_distance = 0;

        // BFS from each node to find max distance
        for start_id in self.topology.keys() {
            let mut visited = vec![false; 9];
            let mut queue = vec![(start_id, 0)];

            while let Some((current_id, dist)) = queue.pop() {
                if visited[*current_id] {
                    continue;
                }
                visited[*current_id] = true;
                max_distance = max_distance.max(dist);

                if let Some(neighbors) = self.topology.get(current_id) {
                    for neighbor_id in neighbors {
                        if !visited[*neighbor_id] {
                            queue.push((neighbor_id, dist + 1));
                        }
                    }
                }
            }
        }

        Some(max_distance)
    }

    /// Schedule next synchronization round
    pub fn schedule_sync_round(&mut self) -> Result<Vec<usize>, String> {
        let active_agents = self.get_active_agents();

        if active_agents.is_empty() {
            return Err("No active agents to synchronize".to_string());
        }

        self.current_round += 1;
        self.round_start = Utc::now();

        Ok(active_agents)
    }

    /// Get round statistics
    pub fn get_round_stats(&self) -> RoundStatistics {
        let active_agents = self.get_active_agents();
        let total_syncs: u64 = self.agents.values().map(|a| a.syncs_completed).sum();
        let total_messages: u64 = self.agents.values().map(|a| a.messages_processed).sum();
        let avg_health: f64 = self.agents.values().map(|a| a.health_score).sum::<f64>()
            / (self.agents.len() as f64).max(1.0);

        RoundStatistics {
            round: self.current_round,
            active_agents: active_agents.len(),
            total_agents: self.agents.len(),
            total_syncs,
            total_messages,
            average_health: avg_health,
            round_duration: Utc::now()
                .signed_duration_since(self.round_start)
                .num_milliseconds(),
        }
    }
}

impl Default for OrchestrationState {
    fn default() -> Self {
        Self::new()
    }
}

/// Round statistics
#[derive(Debug, Clone)]
pub struct RoundStatistics {
    pub round: u64,
    pub active_agents: usize,
    pub total_agents: usize,
    pub total_syncs: u64,
    pub total_messages: u64,
    pub average_health: f64,
    pub round_duration: i64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_agent() {
        let mut state = OrchestrationState::new();
        let result = state.register_agent(0, vec![1, 2]);
        assert!(result.is_ok());
        assert_eq!(state.agents.len(), 1);
    }

    #[test]
    fn test_duplicate_registration() {
        let mut state = OrchestrationState::new();
        state.register_agent(0, vec![1, 2]).unwrap();
        let result = state.register_agent(0, vec![1, 2]);
        assert!(result.is_err());
    }

    #[test]
    fn test_deregister_agent() {
        let mut state = OrchestrationState::new();
        state.register_agent(0, vec![1, 2]).unwrap();
        let result = state.deregister_agent(0);
        assert!(result.is_ok());
        assert_eq!(state.agents.len(), 0);
    }

    #[test]
    fn test_update_heartbeat() {
        let mut state = OrchestrationState::new();
        state.register_agent(0, vec![1, 2]).unwrap();
        let result = state.update_heartbeat(0);
        assert!(result.is_ok());
    }

    #[test]
    fn test_schedule_sync_round() {
        let mut state = OrchestrationState::new();
        state.register_agent(0, vec![1, 2]).unwrap();
        state.register_agent(1, vec![0, 2]).unwrap();

        let result = state.schedule_sync_round();
        assert!(result.is_ok());
        assert_eq!(state.current_round, 1);
    }

    #[test]
    fn test_get_active_agents() {
        let mut state = OrchestrationState::new();
        state.register_agent(0, vec![1, 2]).unwrap();
        state.register_agent(1, vec![0, 2]).unwrap();

        let active = state.get_active_agents();
        assert_eq!(active.len(), 2);
    }
}
