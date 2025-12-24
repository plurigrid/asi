/*!
    dashboard: Real-Time Network Visualization & Monitoring

    P2 Component: Web-based dashboard for monitoring distributed agent network.
    Integrates data from all P1 components (orchestrator, colors, transduction, timeline)
    to provide real-time insights into network state, message flows, and performance.

    Features:
    - Real-time agent network topology visualization
    - Message flow heatmaps with latency coloring
    - Performance metrics dashboard (latency, throughput, efficiency)
    - Agent health monitoring with automatic failover indicators
    - Historical timeline visualization
    - Interactive e-graph structure browser
*/

use crate::{OrchestrationState, InteractionTimeline, PerformanceMetrics};
use std::collections::HashMap;

/// Dashboard data aggregator
pub struct Dashboard {
    pub title: String,
    pub refresh_interval_ms: u64,
    pub agents_data: Vec<AgentDashboardData>,
    pub network_data: NetworkDashboardData,
    pub performance_data: PerformanceDashboardData,
    pub timeline_data: TimelineDashboardData,
}

/// Per-agent dashboard information
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct AgentDashboardData {
    pub agent_id: usize,
    pub node_id: String,
    pub is_active: bool,
    pub health_score: f64,
    pub color_indicator: String,
    pub neighbors: Vec<usize>,
    pub messages_sent: u64,
    pub messages_received: u64,
    pub syncs_completed: u64,
    pub last_heartbeat_ago_ms: u64,
}

/// Network topology dashboard data
#[derive(Debug, Clone)]
pub struct NetworkDashboardData {
    pub total_agents: usize,
    pub active_agents: usize,
    pub network_diameter: Option<usize>,
    pub avg_connections: f64,
    pub topology_type: String,
    pub message_flows: Vec<MessageFlowDashboard>,
}

/// Message flow visualization
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct MessageFlowDashboard {
    pub source: usize,
    pub target: usize,
    pub message_count: usize,
    pub latency_ms: f64,
    pub throughput_mbps: f64,
    pub flow_color: String,
    pub thickness: f64,
}

/// Performance metrics dashboard
#[derive(Debug, Clone)]
pub struct PerformanceDashboardData {
    pub min_latency_ms: u64,
    pub max_latency_ms: u64,
    pub avg_latency_ms: f64,
    pub p50_latency_ms: f64,
    pub p95_latency_ms: f64,
    pub p99_latency_ms: f64,
    pub total_messages: usize,
    pub total_bytes: u64,
    pub throughput_mbps: f64,
    pub synchronization_efficiency: f64,
    pub convergence_status: String,
}

/// Timeline visualization data
#[derive(Debug, Clone)]
pub struct TimelineDashboardData {
    pub timeline_json: String,
    pub total_events: usize,
    pub event_types: HashMap<String, usize>,
    pub time_range_ms: u64,
}

impl Dashboard {
    pub fn new(title: String) -> Self {
        Self {
            title,
            refresh_interval_ms: 1000,
            agents_data: Vec::new(),
            network_data: NetworkDashboardData {
                total_agents: 0,
                active_agents: 0,
                network_diameter: None,
                avg_connections: 0.0,
                topology_type: "Unknown".to_string(),
                message_flows: Vec::new(),
            },
            performance_data: PerformanceDashboardData {
                min_latency_ms: 0,
                max_latency_ms: 0,
                avg_latency_ms: 0.0,
                p50_latency_ms: 0.0,
                p95_latency_ms: 0.0,
                p99_latency_ms: 0.0,
                total_messages: 0,
                total_bytes: 0,
                throughput_mbps: 0.0,
                synchronization_efficiency: 0.0,
                convergence_status: "Computing...".to_string(),
            },
            timeline_data: TimelineDashboardData {
                timeline_json: "[]".to_string(),
                total_events: 0,
                event_types: HashMap::new(),
                time_range_ms: 0,
            },
        }
    }

    /// Update dashboard from orchestration state
    pub fn update_from_orchestration(&mut self, state: &OrchestrationState) {
        self.network_data.total_agents = state.agents.len();
        self.network_data.active_agents = state.get_active_agents().len();
        self.network_data.network_diameter = state.get_network_diameter();

        // Compute average connections
        let total_connections: usize = state
            .topology
            .values()
            .map(|neighbors| neighbors.len())
            .sum();
        self.network_data.avg_connections =
            if state.agents.is_empty() {
                0.0
            } else {
                total_connections as f64 / state.agents.len() as f64
            };

        // Identify Sierpinski lattice
        if self.network_data.avg_connections > 2.5 && self.network_data.avg_connections < 3.5 {
            self.network_data.topology_type = "Sierpinski Lattice".to_string();
        }

        // Update agent data
        self.agents_data.clear();
        for (agent_id, metadata) in &state.agents {
            let health_color = Self::health_to_color(metadata.health_score);

            let agent_data = AgentDashboardData {
                agent_id: *agent_id,
                node_id: format!("node_{}", agent_id),
                is_active: metadata.is_active,
                health_score: metadata.health_score,
                color_indicator: health_color,
                neighbors: state
                    .topology
                    .get(agent_id)
                    .cloned()
                    .unwrap_or_default(),
                messages_sent: 0,
                messages_received: 0,
                syncs_completed: metadata.syncs_completed,
                last_heartbeat_ago_ms: 0,
            };

            self.agents_data.push(agent_data);
        }

        // Sort agents by ID
        self.agents_data.sort_by_key(|a| a.agent_id);
    }

    /// Update dashboard from timeline
    pub fn update_from_timeline(&mut self, timeline: &InteractionTimeline) {
        self.performance_data.min_latency_ms = timeline.metrics.min_latency_ms;
        self.performance_data.max_latency_ms = timeline.metrics.max_latency_ms;
        self.performance_data.avg_latency_ms = timeline.metrics.avg_latency_ms;
        self.performance_data.p50_latency_ms = timeline.metrics.p50_latency_ms;
        self.performance_data.p95_latency_ms = timeline.metrics.p95_latency_ms;
        self.performance_data.p99_latency_ms = timeline.metrics.p99_latency_ms;
        self.performance_data.total_messages = timeline.metrics.total_messages;
        self.performance_data.total_bytes = timeline.metrics.total_bytes_transferred;
        self.performance_data.synchronization_efficiency =
            timeline.metrics.synchronization_efficiency;

        // Update message flows
        self.network_data.message_flows.clear();
        for flow in timeline.flow_summary() {
            let latency = self.performance_data.avg_latency_ms;
            let flow_color = Self::latency_to_color(latency);
            let thickness = (flow.2 as f64).log10().max(1.0);

            self.network_data.message_flows.push(MessageFlowDashboard {
                source: flow.0,
                target: flow.1,
                message_count: flow.2,
                latency_ms: latency,
                throughput_mbps: flow.3,
                flow_color,
                thickness,
            });
        }

        // Update timeline data
        self.timeline_data.total_events = timeline.metrics.total_events;
        self.timeline_data.event_types = timeline.event_counts_by_type();
        self.timeline_data.time_range_ms = timeline.metrics.timeline_span_ms;
        self.timeline_data.timeline_json = timeline.export_timeline_json();

        // Determine convergence status
        self.performance_data.convergence_status = if self.performance_data.synchronization_efficiency > 0.8 {
            "Converged".to_string()
        } else if self.performance_data.synchronization_efficiency > 0.5 {
            "Converging".to_string()
        } else {
            "Synchronizing".to_string()
        };
    }

    /// Convert health score to color
    fn health_to_color(health: f64) -> String {
        match health {
            h if h >= 0.8 => "green".to_string(),
            h if h >= 0.5 => "yellow".to_string(),
            h if h >= 0.2 => "orange".to_string(),
            _ => "red".to_string(),
        }
    }

    /// Convert latency to color (lower is better)
    fn latency_to_color(latency: f64) -> String {
        match latency {
            l if l < 10.0 => "green".to_string(),
            l if l < 50.0 => "yellow".to_string(),
            l if l < 100.0 => "orange".to_string(),
            _ => "red".to_string(),
        }
    }

    /// Generate HTML dashboard
    pub fn render_html(&self) -> String {
        format!(
            r#"<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{}</title>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; background: #0f1419; color: #e0e0e0; }}
        .container {{ max-width: 1400px; margin: 0 auto; padding: 20px; }}
        h1 {{ color: #00d9ff; margin-bottom: 30px; }}
        h2 {{ color: #00b8cc; margin: 20px 0 10px; }}

        .grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 20px; margin-bottom: 20px; }}
        .card {{ background: #1a1f2e; border: 1px solid #2a3f5f; border-radius: 8px; padding: 20px; }}
        .card h3 {{ color: #00d9ff; margin-bottom: 10px; }}

        .metric {{ margin: 10px 0; display: flex; justify-content: space-between; }}
        .metric-label {{ color: #888; }}
        .metric-value {{ color: #00ff88; font-weight: bold; font-family: 'Monaco', monospace; }}

        .agent-list {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(200px, 1fr)); gap: 10px; }}
        .agent-item {{ background: #242a3a; padding: 15px; border-radius: 6px; border-left: 4px solid #00d9ff; }}
        .agent-id {{ font-weight: bold; color: #00d9ff; }}
        .agent-status {{ font-size: 0.85em; color: #888; margin-top: 5px; }}

        .health-indicator {{ width: 12px; height: 12px; border-radius: 50%; display: inline-block; margin-right: 5px; }}
        .health-green {{ background: #00ff88; }}
        .health-yellow {{ background: #ffff00; }}
        .health-orange {{ background: #ff8800; }}
        .health-red {{ background: #ff0000; }}

        .timeline {{ background: #242a3a; padding: 15px; border-radius: 6px; margin-top: 10px; }}
        .timeline-item {{ padding: 5px 0; border-bottom: 1px solid #3a4a5a; font-size: 0.9em; }}

        .convergence {{ background: #1a3a2e; border-left: 4px solid #00ff88; padding: 15px; border-radius: 6px; }}
        .convergence.warning {{ background: #3a2e1a; border-left-color: #ffff00; }}
        .convergence.error {{ background: #3a1a1a; border-left-color: #ff0000; }}
    </style>
</head>
<body>
    <div class="container">
        <h1>🌐 CRDT Agent Network Dashboard</h1>

        <!-- Network Overview -->
        <div class="card">
            <h2>Network Overview</h2>
            <div class="grid">
                <div>
                    <div class="metric">
                        <span class="metric-label">Total Agents:</span>
                        <span class="metric-value">{}</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">Active:</span>
                        <span class="metric-value">{}</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">Avg Connections:</span>
                        <span class="metric-value">{:.2}</span>
                    </div>
                </div>
                <div>
                    <div class="metric">
                        <span class="metric-label">Topology:</span>
                        <span class="metric-value">{}</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">Network Diameter:</span>
                        <span class="metric-value">{}</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">Refresh: </span>
                        <span class="metric-value">{}ms</span>
                    </div>
                </div>
            </div>
        </div>

        <!-- Agent Status -->
        <h2>Agent Status</h2>
        <div class="agent-list">
            {}
        </div>

        <!-- Performance Metrics -->
        <div class="card">
            <h2>Performance Metrics</h2>
            <div class="grid">
                <div>
                    <div class="metric">
                        <span class="metric-label">Min Latency:</span>
                        <span class="metric-value">{}ms</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">Avg Latency:</span>
                        <span class="metric-value">{:.1}ms</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">Max Latency:</span>
                        <span class="metric-value">{}ms</span>
                    </div>
                </div>
                <div>
                    <div class="metric">
                        <span class="metric-label">P50:</span>
                        <span class="metric-value">{:.1}ms</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">P95:</span>
                        <span class="metric-value">{:.1}ms</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">P99:</span>
                        <span class="metric-value">{:.1}ms</span>
                    </div>
                </div>
                <div>
                    <div class="metric">
                        <span class="metric-label">Total Messages:</span>
                        <span class="metric-value">{}</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">Total Data:</span>
                        <span class="metric-value">{:.2}MB</span>
                    </div>
                    <div class="metric">
                        <span class="metric-label">Efficiency:</span>
                        <span class="metric-value">{:.1}%</span>
                    </div>
                </div>
            </div>
        </div>

        <!-- Convergence Status -->
        <div class="convergence {}">
            <h3>⚡ Convergence Status: {}</h3>
            <p>Timeline Span: {}ms | Total Events: {}</p>
        </div>

        <!-- Message Flow Summary -->
        <div class="card">
            <h2>Message Flows</h2>
            <table style="width: 100%; border-collapse: collapse; font-size: 0.9em;">
                <tr style="border-bottom: 1px solid #3a4a5a; text-align: left;">
                    <th style="padding: 8px;">Source</th>
                    <th style="padding: 8px;">Target</th>
                    <th style="padding: 8px;">Messages</th>
                    <th style="padding: 8px;">Latency</th>
                    <th style="padding: 8px;">Throughput</th>
                </tr>
                {}
            </table>
        </div>
    </div>
</body>
</html>"#,
            self.title,
            self.network_data.total_agents,
            self.network_data.active_agents,
            self.network_data.avg_connections,
            self.network_data.topology_type,
            self.network_data.network_diameter.map(|d| d.to_string()).unwrap_or_else(|| "Unknown".to_string()),
            self.refresh_interval_ms,
            self.render_agent_items(),
            self.performance_data.min_latency_ms,
            self.performance_data.avg_latency_ms,
            self.performance_data.max_latency_ms,
            self.performance_data.p50_latency_ms,
            self.performance_data.p95_latency_ms,
            self.performance_data.p99_latency_ms,
            self.performance_data.total_messages,
            self.performance_data.total_bytes as f64 / (1024.0 * 1024.0),
            self.performance_data.synchronization_efficiency * 100.0,
            Self::convergence_css_class(&self.performance_data.convergence_status),
            self.performance_data.convergence_status,
            self.timeline_data.time_range_ms,
            self.timeline_data.total_events,
            self.render_message_flows()
        )
    }

    /// Render agent status items
    fn render_agent_items(&self) -> String {
        self.agents_data
            .iter()
            .map(|agent| {
                let health_class = format!("health-{}", agent.color_indicator);
                format!(
                    r#"<div class="agent-item">
                    <div class="agent-id"><span class="health-indicator {}"></span>Agent {}</div>
                    <div class="agent-status">
                        Status: {}
                        <br>Health: {:.1}%
                        <br>Syncs: {}
                    </div>
                </div>"#,
                    health_class,
                    agent.agent_id,
                    if agent.is_active { "🟢 Active" } else { "🔴 Inactive" },
                    agent.health_score * 100.0,
                    agent.syncs_completed
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Render message flow table rows
    fn render_message_flows(&self) -> String {
        self.network_data
            .message_flows
            .iter()
            .map(|flow| {
                format!(
                    r#"<tr style="border-bottom: 1px solid #3a4a5a;">
                    <td style="padding: 8px;">{}</td>
                    <td style="padding: 8px;">{}</td>
                    <td style="padding: 8px;">{}</td>
                    <td style="padding: 8px; color: {};">{:.1}ms</td>
                    <td style="padding: 8px;">{:.2} Mbps</td>
                </tr>"#,
                    flow.source, flow.target, flow.message_count, flow.flow_color, flow.latency_ms, flow.throughput_mbps
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Get CSS class for convergence status
    fn convergence_css_class(status: &str) -> String {
        match status {
            "Converged" => "".to_string(),
            "Converging" => "warning".to_string(),
            _ => "warning".to_string(),
        }
    }

    /// Generate JSON for API responses
    pub fn render_json(&self) -> String {
        format!(
            r#"{{
  "title": "{}",
  "network": {{
    "total_agents": {},
    "active_agents": {},
    "topology": "{}",
    "diameter": {}
  }},
  "performance": {{
    "min_latency_ms": {},
    "avg_latency_ms": {:.1},
    "max_latency_ms": {},
    "p95_latency_ms": {:.1},
    "p99_latency_ms": {:.1},
    "total_messages": {},
    "total_bytes": {},
    "efficiency": {:.2}
  }},
  "convergence": "{}",
  "agents": {},
  "flows": {}
}}"#,
            self.title,
            self.network_data.total_agents,
            self.network_data.active_agents,
            self.network_data.topology_type,
            self.network_data.network_diameter.unwrap_or(0),
            self.performance_data.min_latency_ms,
            self.performance_data.avg_latency_ms,
            self.performance_data.max_latency_ms,
            self.performance_data.p95_latency_ms,
            self.performance_data.p99_latency_ms,
            self.performance_data.total_messages,
            self.performance_data.total_bytes,
            self.performance_data.synchronization_efficiency,
            self.performance_data.convergence_status,
            serde_json::to_string(&self.agents_data).unwrap_or_default(),
            serde_json::to_string(&self.network_data.message_flows).unwrap_or_default()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dashboard_creation() {
        let dashboard = Dashboard::new("Test Dashboard".to_string());
        assert_eq!(dashboard.title, "Test Dashboard");
        assert_eq!(dashboard.network_data.total_agents, 0);
    }

    #[test]
    fn test_health_to_color() {
        assert_eq!(Dashboard::health_to_color(0.9), "green");
        assert_eq!(Dashboard::health_to_color(0.6), "yellow");
        assert_eq!(Dashboard::health_to_color(0.3), "orange");
        assert_eq!(Dashboard::health_to_color(0.1), "red");
    }

    #[test]
    fn test_latency_to_color() {
        assert_eq!(Dashboard::latency_to_color(5.0), "green");
        assert_eq!(Dashboard::latency_to_color(30.0), "yellow");
        assert_eq!(Dashboard::latency_to_color(75.0), "orange");
        assert_eq!(Dashboard::latency_to_color(200.0), "red");
    }

    #[test]
    fn test_render_html_contains_title() {
        let dashboard = Dashboard::new("My Dashboard".to_string());
        let html = dashboard.render_html();
        assert!(html.contains("My Dashboard"));
        assert!(html.contains("<!DOCTYPE html>"));
    }

    #[test]
    fn test_render_json_contains_structure() {
        let dashboard = Dashboard::new("API Dashboard".to_string());
        let json = dashboard.render_json();
        assert!(json.contains("\"title\""));
        assert!(json.contains("\"network\""));
        assert!(json.contains("\"performance\""));
    }

    #[test]
    fn test_agent_data_creation() {
        let agent = AgentDashboardData {
            agent_id: 0,
            node_id: "node_0".to_string(),
            is_active: true,
            health_score: 0.95,
            color_indicator: "green".to_string(),
            neighbors: vec![1, 2],
            messages_sent: 100,
            messages_received: 100,
            syncs_completed: 5,
            last_heartbeat_ago_ms: 100,
        };

        assert_eq!(agent.agent_id, 0);
        assert!(agent.is_active);
        assert_eq!(agent.neighbors.len(), 2);
    }

    #[test]
    fn test_message_flow_dashboard() {
        let flow = MessageFlowDashboard {
            source: 0,
            target: 1,
            message_count: 100,
            latency_ms: 25.5,
            throughput_mbps: 10.2,
            flow_color: "green".to_string(),
            thickness: 2.5,
        };

        assert_eq!(flow.source, 0);
        assert_eq!(flow.target, 1);
        assert_eq!(flow.message_count, 100);
    }
}
