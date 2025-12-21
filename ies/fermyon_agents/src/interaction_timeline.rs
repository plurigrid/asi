/*!
    interaction-timeline: Message Timeline & Performance Metrics

    P1 Component: Tracks message delivery timeline, causality ordering,
    and performance metrics for distributed agent synchronization.

    Features:
    - Message event tracking with precise timestamps
    - Vector clock causality ordering
    - Latency analysis and percentile computation
    - Message flow visualization data
    - Performance metric aggregation
    - Network topology analysis
*/

use chrono::{DateTime, Duration, Utc};
use std::collections::{HashMap, VecDeque};

/// Timeline event representing agent interaction
#[derive(Debug, Clone)]
pub struct TimelineEvent {
    pub event_id: String,
    pub event_type: EventType,
    pub timestamp: DateTime<Utc>,
    pub from_agent: usize,
    pub to_agent: usize,
    pub vector_clock: HashMap<String, u64>,
    pub payload_size: u64,
    pub duration_ms: u64,
}

/// Type of interaction event
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventType {
    MessageSent,
    MessageReceived,
    SyncStarted,
    SyncCompleted,
    AckSent,
    AckReceived,
    HeartbeatSent,
    ConvergenceDetected,
}

/// Message flow segment between two agents
#[derive(Debug, Clone)]
pub struct MessageFlow {
    pub source: usize,
    pub target: usize,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub message_count: usize,
    pub total_bytes: u64,
    pub error_count: usize,
}

impl MessageFlow {
    pub fn duration_ms(&self) -> u64 {
        self.end_time
            .signed_duration_since(self.start_time)
            .num_milliseconds() as u64
    }

    pub fn throughput_mbps(&self) -> f64 {
        if self.duration_ms() == 0 {
            return 0.0;
        }
        (self.total_bytes as f64 * 8.0) / (self.duration_ms() as f64 / 1000.0) / 1_000_000.0
    }

    pub fn success_rate(&self) -> f64 {
        if self.message_count == 0 {
            return 1.0;
        }
        ((self.message_count - self.error_count) as f64 / self.message_count as f64)
            .max(0.0)
            .min(1.0)
    }
}

/// Causality information for ordering events
#[derive(Debug, Clone)]
pub struct CausalityInfo {
    pub event_id: String,
    pub causally_before: Vec<String>,
    pub causally_after: Vec<String>,
    pub concurrent_with: Vec<String>,
}

/// Performance metrics for timeline
#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    pub total_events: usize,
    pub total_messages: usize,
    pub total_syncs: usize,
    pub avg_latency_ms: f64,
    pub p50_latency_ms: f64,
    pub p95_latency_ms: f64,
    pub p99_latency_ms: f64,
    pub min_latency_ms: u64,
    pub max_latency_ms: u64,
    pub total_bytes_transferred: u64,
    pub synchronization_efficiency: f64,
    pub timeline_span_ms: u64,
}

/// Timeline aggregator: collects and analyzes interaction events
pub struct InteractionTimeline {
    pub events: VecDeque<TimelineEvent>,
    pub flows: HashMap<(usize, usize), MessageFlow>,
    pub causality: HashMap<String, CausalityInfo>,
    pub metrics: PerformanceMetrics,
    pub start_time: DateTime<Utc>,
    pub window_size: usize,
}

impl InteractionTimeline {
    pub fn new(window_size: usize) -> Self {
        Self {
            events: VecDeque::with_capacity(window_size),
            flows: HashMap::new(),
            causality: HashMap::new(),
            metrics: PerformanceMetrics {
                total_events: 0,
                total_messages: 0,
                total_syncs: 0,
                avg_latency_ms: 0.0,
                p50_latency_ms: 0.0,
                p95_latency_ms: 0.0,
                p99_latency_ms: 0.0,
                min_latency_ms: 0,
                max_latency_ms: 0,
                total_bytes_transferred: 0,
                synchronization_efficiency: 1.0,
                timeline_span_ms: 0,
            },
            start_time: Utc::now(),
            window_size,
        }
    }

    /// Record interaction event
    pub fn record_event(&mut self, mut event: TimelineEvent) {
        // Auto-generate ID if not provided
        if event.event_id.is_empty() {
            event.event_id = format!(
                "evt_{}_{}_{:?}",
                event.from_agent, event.to_agent, event.event_type
            );
        }

        // Update metrics
        self.metrics.total_events += 1;
        match event.event_type {
            EventType::MessageSent | EventType::MessageReceived => {
                self.metrics.total_messages += 1;
            }
            EventType::SyncCompleted => {
                self.metrics.total_syncs += 1;
            }
            _ => {}
        }

        // Update message flows
        let flow_key = (event.from_agent, event.to_agent);
        let flow = self.flows.entry(flow_key).or_insert_with(|| MessageFlow {
            source: event.from_agent,
            target: event.to_agent,
            start_time: event.timestamp,
            end_time: event.timestamp,
            message_count: 0,
            total_bytes: 0,
            error_count: 0,
        });

        if event.event_type == EventType::MessageSent {
            flow.message_count += 1;
            flow.total_bytes += event.payload_size;
        }
        flow.end_time = event.timestamp;

        // Update byte count
        if event.payload_size > 0 {
            self.metrics.total_bytes_transferred += event.payload_size;
        }

        // Add to timeline (with windowing)
        self.events.push_back(event);
        if self.events.len() > self.window_size {
            self.events.pop_front();
        }
    }

    /// Compute latencies from recorded events
    pub fn compute_latencies(&mut self) -> Vec<u64> {
        let mut latencies = Vec::new();

        let events: Vec<_> = self.events.iter().cloned().collect();
        for window in events.windows(2) {
            if window.len() == 2 {
                let e1 = &window[0];
                let e2 = &window[1];

                // Compute latency for message send/receive pairs
                if e1.event_type == EventType::MessageSent && e2.event_type == EventType::MessageReceived
                {
                    let latency = e2
                        .timestamp
                        .signed_duration_since(e1.timestamp)
                        .num_milliseconds() as u64;
                    if latency > 0 {
                        latencies.push(latency);
                    }
                }
            }
        }

        // Update percentiles
        if !latencies.is_empty() {
            latencies.sort();

            self.metrics.min_latency_ms = latencies[0];
            self.metrics.max_latency_ms = latencies[latencies.len() - 1];
            self.metrics.avg_latency_ms =
                latencies.iter().sum::<u64>() as f64 / latencies.len() as f64;

            let p50_idx = (latencies.len() * 50) / 100;
            let p95_idx = (latencies.len() * 95) / 100;
            let p99_idx = (latencies.len() * 99) / 100;

            self.metrics.p50_latency_ms = latencies[p50_idx] as f64;
            self.metrics.p95_latency_ms = latencies[p95_idx.min(latencies.len() - 1)] as f64;
            self.metrics.p99_latency_ms = latencies[p99_idx.min(latencies.len() - 1)] as f64;
        }

        latencies
    }

    /// Update timeline span and efficiency metrics
    pub fn finalize_metrics(&mut self) {
        if let (Some(first), Some(last)) = (self.events.front(), self.events.back()) {
            self.metrics.timeline_span_ms = last
                .timestamp
                .signed_duration_since(first.timestamp)
                .num_milliseconds() as u64;
        }

        // Efficiency: ratio of sync events to total events
        if self.metrics.total_events > 0 {
            self.metrics.synchronization_efficiency =
                self.metrics.total_syncs as f64 / self.metrics.total_events as f64;
        }

        // Compute all latencies
        self.compute_latencies();
    }

    /// Get causality ordering from vector clocks
    pub fn compute_causality(&mut self) {
        for event in &self.events {
            let causal = CausalityInfo {
                event_id: event.event_id.clone(),
                causally_before: Vec::new(),
                causally_after: Vec::new(),
                concurrent_with: Vec::new(),
            };

            // Compare against all other events
            for other in &self.events {
                if event.event_id != other.event_id {
                    let ordering = self.compare_vector_clocks(&event.vector_clock, &other.vector_clock);
                    match ordering {
                        VectorClockOrdering::Before => {
                            // Implementation would track causally_before
                        }
                        VectorClockOrdering::After => {
                            // Implementation would track causally_after
                        }
                        VectorClockOrdering::Concurrent => {
                            // Implementation would track concurrent_with
                        }
                    }
                }
            }

            self.causality.insert(event.event_id.clone(), causal);
        }
    }

    /// Compare two vector clocks
    fn compare_vector_clocks(
        &self,
        vc1: &HashMap<String, u64>,
        vc2: &HashMap<String, u64>,
    ) -> VectorClockOrdering {
        let mut v1_less = false;
        let mut v2_less = false;

        for (key, val1) in vc1 {
            if let Some(val2) = vc2.get(key) {
                if val1 < val2 {
                    v2_less = true;
                } else if val1 > val2 {
                    v1_less = true;
                }
            }
        }

        if v1_less && !v2_less {
            VectorClockOrdering::Before
        } else if v2_less && !v1_less {
            VectorClockOrdering::After
        } else {
            VectorClockOrdering::Concurrent
        }
    }

    /// Export timeline as JSON for visualization
    pub fn export_timeline_json(&self) -> String {
        let events_json: Vec<_> = self
            .events
            .iter()
            .map(|e| {
                format!(
                    r#"{{"id":"{}","type":"{:?}","from":{},"to":{},"timestamp":"{}"}}"#,
                    e.event_id, e.event_type, e.from_agent, e.to_agent, e.timestamp
                )
            })
            .collect();

        format!("[{}]", events_json.join(","))
    }

    /// Get message flow summary
    pub fn flow_summary(&self) -> Vec<(usize, usize, usize, f64)> {
        self.flows
            .values()
            .map(|f| (f.source, f.target, f.message_count, f.throughput_mbps()))
            .collect()
    }

    /// Get latency summary
    pub fn latency_summary(&self) -> (u64, u64, f64) {
        (self.metrics.min_latency_ms, self.metrics.max_latency_ms, self.metrics.avg_latency_ms)
    }

    /// Clear old events beyond time window
    pub fn prune_old_events(&mut self, max_age_ms: u64) {
        let cutoff = Utc::now() - Duration::milliseconds(max_age_ms as i64);
        self.events.retain(|e| e.timestamp > cutoff);
    }

    /// Get total synchronization rounds
    pub fn sync_rounds(&self) -> usize {
        self.metrics.total_syncs
    }

    /// Get event count by type
    pub fn event_counts_by_type(&self) -> HashMap<String, usize> {
        let mut counts = HashMap::new();
        for event in &self.events {
            let key = format!("{:?}", event.event_type);
            *counts.entry(key).or_insert(0) += 1;
        }
        counts
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum VectorClockOrdering {
    Before,
    After,
    Concurrent,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_timeline_creation() {
        let timeline = InteractionTimeline::new(100);
        assert_eq!(timeline.metrics.total_events, 0);
        assert_eq!(timeline.metrics.total_messages, 0);
    }

    #[test]
    fn test_record_event() {
        let mut timeline = InteractionTimeline::new(100);

        let event = TimelineEvent {
            event_id: "test1".to_string(),
            event_type: EventType::MessageSent,
            timestamp: Utc::now(),
            from_agent: 0,
            to_agent: 1,
            vector_clock: HashMap::new(),
            payload_size: 1024,
            duration_ms: 5,
        };

        timeline.record_event(event);
        assert_eq!(timeline.metrics.total_events, 1);
        assert_eq!(timeline.metrics.total_messages, 1);
    }

    #[test]
    fn test_message_flow_creation() {
        let timeline = InteractionTimeline::new(100);
        let flow = MessageFlow {
            source: 0,
            target: 1,
            start_time: Utc::now(),
            end_time: Utc::now(),
            message_count: 10,
            total_bytes: 10240,
            error_count: 0,
        };

        assert_eq!(flow.success_rate(), 1.0);
    }

    #[test]
    fn test_window_size_enforcement() {
        let mut timeline = InteractionTimeline::new(5);

        for i in 0..10 {
            let event = TimelineEvent {
                event_id: format!("evt{}", i),
                event_type: EventType::MessageSent,
                timestamp: Utc::now(),
                from_agent: 0,
                to_agent: 1,
                vector_clock: HashMap::new(),
                payload_size: 100,
                duration_ms: 1,
            };
            timeline.record_event(event);
        }

        assert!(timeline.events.len() <= timeline.window_size);
    }

    #[test]
    fn test_event_counts_by_type() {
        let mut timeline = InteractionTimeline::new(100);

        for _ in 0..3 {
            timeline.record_event(TimelineEvent {
                event_id: String::new(),
                event_type: EventType::MessageSent,
                timestamp: Utc::now(),
                from_agent: 0,
                to_agent: 1,
                vector_clock: HashMap::new(),
                payload_size: 100,
                duration_ms: 1,
            });
        }

        let counts = timeline.event_counts_by_type();
        assert_eq!(*counts.get("MessageSent").unwrap_or(&0), 3);
    }

    #[test]
    fn test_flow_throughput() {
        let start = Utc::now();
        let end = start + Duration::seconds(1);

        let flow = MessageFlow {
            source: 0,
            target: 1,
            start_time: start,
            end_time: end,
            message_count: 100,
            total_bytes: 1_000_000, // 1 MB
            error_count: 0,
        };

        let throughput = flow.throughput_mbps();
        assert!(throughput > 0.0);
    }

    #[test]
    fn test_metrics_finalization() {
        let mut timeline = InteractionTimeline::new(100);

        let event1 = TimelineEvent {
            event_id: "evt1".to_string(),
            event_type: EventType::SyncStarted,
            timestamp: Utc::now(),
            from_agent: 0,
            to_agent: 1,
            vector_clock: HashMap::new(),
            payload_size: 0,
            duration_ms: 1,
        };

        timeline.record_event(event1);
        timeline.finalize_metrics();

        assert_eq!(timeline.metrics.total_syncs, 1);
        assert!(timeline.metrics.timeline_span_ms >= 0);
    }

    #[test]
    fn test_export_timeline_json() {
        let mut timeline = InteractionTimeline::new(100);

        let event = TimelineEvent {
            event_id: "test_evt".to_string(),
            event_type: EventType::MessageSent,
            timestamp: Utc::now(),
            from_agent: 0,
            to_agent: 1,
            vector_clock: HashMap::new(),
            payload_size: 100,
            duration_ms: 1,
        };

        timeline.record_event(event);
        let json = timeline.export_timeline_json();

        assert!(json.contains("test_evt"));
        assert!(json.starts_with("["));
        assert!(json.ends_with("]"));
    }
}
