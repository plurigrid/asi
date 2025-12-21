/*!
    Integration Tests: Full System Validation

    Tests for complete CRDT agent network pipeline:
    orchestration → colors → transduction → stream operations → timeline → dashboard
*/

// Import all public types from the library
use fermyon_agents::{
    // Core types
    Color, ENode, CRDTEGraph, ServerlessAgent, AgentMessage, MessageType,
    // P0 components
    StreamRed, StreamBlue, StreamGreen,
    // P1 components
    OrchestrationState, AgentMetadata, ColorAssigner, Transducer,
    RewriteRule, PatternExpr, TopologicalPattern, Polarity as RewritePolarity,
    InteractionTimeline, TimelineEvent, EventType, PerformanceMetrics,
    // P2 component
    Dashboard,
};
use std::collections::HashMap;
use chrono::Utc;

// ═══════════════════════════════════════════════════════════════════════════════
// Test 1: Basic Component Initialization
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_all_components_initialize() {
    // Initialize P0 components
    let _stream_red = StreamRed::new("test".to_string(), 2, true);
    let _stream_blue = StreamBlue::new("test".to_string(), 2, false);
    let _stream_green = StreamGreen::new("test".to_string(), true);

    // Initialize P1 components
    let _orchestration = OrchestrationState::new();
    let mut _colors = ColorAssigner::new(42);
    let mut _transducer = Transducer::new();
    let _timeline = InteractionTimeline::new(1000);

    // Initialize P2 component
    let _dashboard = Dashboard::new("Integration Test".to_string());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 2: Orchestration & Agent Management
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_orchestration_with_9_agents() {
    let mut orchestration = OrchestrationState::new();

    // Register 9 agents in Sierpinski lattice topology
    let topology = vec![
        (0, vec![1, 3]),      // Layer 1
        (1, vec![0, 2, 4]),
        (2, vec![1, 5]),
        (3, vec![0, 4, 6]),   // Layer 2
        (4, vec![1, 3, 5, 7]),
        (5, vec![2, 4, 8]),
        (6, vec![3, 7]),      // Layer 3
        (7, vec![4, 6, 8]),
        (8, vec![5, 7]),
    ];

    // Register all agents
    for (agent_id, neighbors) in topology.clone() {
        let result = orchestration.register_agent(agent_id, neighbors);
        assert!(result.is_ok(), "Failed to register agent {}", agent_id);
    }

    // Verify all registered
    assert_eq!(orchestration.agents.len(), 9);
    assert_eq!(orchestration.topology.len(), 9);

    // Get network diameter
    let diameter = orchestration.get_network_diameter();
    assert_eq!(diameter, Some(3), "Sierpinski lattice should have diameter 3");

    // Get active agents
    let active = orchestration.get_active_agents();
    assert_eq!(active.len(), 9, "All agents should be active");

    // Schedule sync round
    let result = orchestration.schedule_sync_round();
    assert!(result.is_ok());
    assert_eq!(orchestration.current_round, 1);

    // Get round stats
    let stats = orchestration.get_round_stats();
    assert_eq!(stats.active_agents, 9);
    assert_eq!(stats.round, 1);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 3: Color Assignment & Gadget Selection
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_color_assignment_determinism() {
    let mut assigner1 = ColorAssigner::new(42);
    let mut assigner2 = ColorAssigner::new(42);
    let mut assigner3 = ColorAssigner::new(99);

    // Same seed → same color
    let color1a = assigner1.assign_color("append");
    let color2a = assigner2.assign_color("append");
    assert_eq!(color1a, color2a, "Same seed should produce same color");

    // Different seed → likely different (not guaranteed but probabilistically true)
    let color3a = assigner3.assign_color("append");
    // Note: 1/3 chance they're the same, so we don't assert inequality

    // Priority ordering
    assigner1.color_cache.insert("red_op".to_string(), Color::Red);
    assigner1.color_cache.insert("green_op".to_string(), Color::Green);
    assigner1.color_cache.insert("blue_op".to_string(), Color::Blue);

    assert_eq!(assigner1.priority_for_operator("red_op"), 30);
    assert_eq!(assigner1.priority_for_operator("green_op"), 20);
    assert_eq!(assigner1.priority_for_operator("blue_op"), 10);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 4: E-Graph Operations with Color Constraints
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_egraph_3coloring_constraints() {
    let mut egraph = CRDTEGraph::new();

    // Add GREEN node (base)
    let green_node = ENode::new("identity".to_string(), vec![], Color::Green);
    let green_id = egraph.add_node(green_node).unwrap();

    // Add RED node with GREEN child (valid)
    let red_node = ENode::new("assoc".to_string(), vec![green_id.clone()], Color::Red);
    let red_id = egraph.add_node(red_node).unwrap();

    // Add BLUE node with GREEN child (valid)
    let blue_node = ENode::new("distrib".to_string(), vec![green_id.clone()], Color::Blue);
    let blue_id = egraph.add_node(blue_node).unwrap();

    // Verify 3-coloring constraints
    assert!(StreamGreen::verify_three_coloring(&egraph).is_ok());

    // Count colors
    let (red, blue, green) = StreamGreen::color_distribution(&egraph);
    assert_eq!(red, 1);
    assert_eq!(blue, 1);
    assert_eq!(green, 1);

    // Verify color restrictions at node level
    assert!(StreamRed::verify_children_colors(&[Color::Red, Color::Green]));
    assert!(StreamBlue::verify_children_colors(&[Color::Blue, Color::Green]));
    assert!(StreamGreen::verify_children_colors(&[Color::Red, Color::Blue]));
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 5: Pattern Transduction & Rule Generation
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_pattern_transduction_pipeline() {
    let mut transducer = Transducer::new();

    // Register patterns
    let pattern1 = TopologicalPattern {
        name: "associativity".to_string(),
        source_pattern: PatternExpr::Var("x".to_string()),
        target_pattern: PatternExpr::Var("y".to_string()),
        constraints: vec![],
        polarity: RewritePolarity::Symmetric,
        priority: 20,
    };

    transducer.register_pattern(pattern1);
    assert_eq!(transducer.pattern_count(), 1);

    // Transduce pattern to rule
    let rule = transducer.transduce("associativity");
    assert!(rule.is_ok());
    assert_eq!(transducer.rule_count(), 1);

    // Generate code for rule
    let rule_obj = rule.unwrap();
    let code = transducer.codegen_rule(&rule_obj);
    assert!(code.contains("apply_rewrite"));
    assert!(code.contains("CRDTEGraph"));

    // Schedule rules
    let scheduled = transducer.schedule_rules(&CRDTEGraph::new());
    assert_eq!(scheduled.len(), 1);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 6: Message Timeline & Performance Metrics
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_timeline_event_collection() {
    let mut timeline = InteractionTimeline::new(1000);

    // Record multiple events
    for i in 0..10 {
        let event = TimelineEvent {
            event_id: format!("evt_{}", i),
            event_type: if i % 2 == 0 {
                EventType::MessageSent
            } else {
                EventType::MessageReceived
            },
            timestamp: Utc::now(),
            from_agent: i % 9,
            to_agent: (i + 1) % 9,
            vector_clock: HashMap::new(),
            payload_size: 1024,
            duration_ms: 5,
        };
        timeline.record_event(event);
    }

    // Verify metrics
    assert_eq!(timeline.metrics.total_events, 10);
    assert_eq!(timeline.metrics.total_messages, 10);
    assert_eq!(timeline.metrics.total_bytes_transferred, 10240);

    // Finalize and check latencies
    timeline.finalize_metrics();
    assert!(timeline.metrics.timeline_span_ms >= 0);

    // Export timeline
    let json = timeline.export_timeline_json();
    assert!(json.contains("evt_"));
    assert!(json.starts_with("["));
    assert!(json.ends_with("]"));
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 7: Dashboard Integration
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_dashboard_aggregation() {
    let mut orchestration = OrchestrationState::new();
    let mut timeline = InteractionTimeline::new(1000);
    let mut dashboard = Dashboard::new("Integration Test Dashboard".to_string());

    // Set up orchestration with agents
    orchestration
        .register_agent(0, vec![1, 2])
        .expect("Failed to register agent 0");
    orchestration
        .register_agent(1, vec![0, 2])
        .expect("Failed to register agent 1");
    orchestration
        .register_agent(2, vec![0, 1])
        .expect("Failed to register agent 2");

    // Record some events
    for i in 0..5 {
        timeline.record_event(TimelineEvent {
            event_id: format!("msg_{}", i),
            event_type: EventType::MessageSent,
            timestamp: Utc::now(),
            from_agent: 0,
            to_agent: 1,
            vector_clock: HashMap::new(),
            payload_size: 512,
            duration_ms: 3,
        });
    }

    timeline.finalize_metrics();

    // Update dashboard from sources
    dashboard.update_from_orchestration(&orchestration);
    dashboard.update_from_timeline(&timeline);

    // Verify dashboard state
    assert_eq!(dashboard.network_data.total_agents, 3);
    assert_eq!(dashboard.network_data.active_agents, 3);
    assert!(dashboard.performance_data.total_messages > 0);
    assert!(dashboard.performance_data.total_bytes > 0);

    // Generate outputs
    let html = dashboard.render_html();
    assert!(html.contains("Integration Test Dashboard"));
    assert!(html.contains("<!DOCTYPE html>"));
    assert!(html.contains("CRDT Agent Network"));

    let json = dashboard.render_json();
    assert!(json.contains("\"title\""));
    assert!(json.contains("\"network\""));
    assert!(json.contains("\"performance\""));
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 8: End-to-End Pipeline
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_full_pipeline_orchestration_to_dashboard() {
    // Step 1: Initialize orchestration
    let mut orchestration = OrchestrationState::new();

    // Step 2: Register 9-agent network
    for i in 0..9 {
        let neighbors = match i {
            0 => vec![1, 3],
            1 => vec![0, 2, 4],
            2 => vec![1, 5],
            3 => vec![0, 4, 6],
            4 => vec![1, 3, 5, 7],
            5 => vec![2, 4, 8],
            6 => vec![3, 7],
            7 => vec![4, 6, 8],
            8 => vec![5, 7],
            _ => vec![],
        };
        orchestration.register_agent(i, neighbors).unwrap();
    }

    // Step 3: Create color assigner and assign colors
    let mut color_assigner = ColorAssigner::new(12345);
    let operators = vec!["append", "concat", "merge", "split", "compose"];
    let mut operator_colors = HashMap::new();

    for op in &operators {
        let color = color_assigner.assign_color(op);
        operator_colors.insert(op.to_string(), color);
    }

    // Step 4: Build e-graph with colored nodes
    let mut egraph = CRDTEGraph::new();

    // Add base nodes
    for (idx, op) in operators.iter().enumerate() {
        let color = operator_colors[*op];
        let node = ENode::new(op.to_string(), vec![], color);
        egraph.add_node(node).unwrap();
    }

    // Verify 3-coloring
    assert!(StreamGreen::verify_three_coloring(&egraph).is_ok());

    // Step 5: Create transducer and register patterns
    let mut transducer = Transducer::new();

    let pattern = TopologicalPattern {
        name: "test_pattern".to_string(),
        source_pattern: PatternExpr::Var("a".to_string()),
        target_pattern: PatternExpr::Var("b".to_string()),
        constraints: vec![],
        polarity: RewritePolarity::Symmetric,
        priority: 15,
    };
    transducer.register_pattern(pattern);

    // Step 6: Transduce patterns to rules
    transducer.transduce("test_pattern").unwrap();

    // Step 7: Create timeline and record events
    let mut timeline = InteractionTimeline::new(100);

    for agent_id in 0..9 {
        let neighbor_id = (agent_id + 1) % 9;
        timeline.record_event(TimelineEvent {
            event_id: format!("sync_{}_{}", agent_id, neighbor_id),
            event_type: EventType::SyncStarted,
            timestamp: Utc::now(),
            from_agent: agent_id,
            to_agent: neighbor_id,
            vector_clock: HashMap::new(),
            payload_size: 0,
            duration_ms: 0,
        });

        timeline.record_event(TimelineEvent {
            event_id: format!("msg_{}_{}", agent_id, neighbor_id),
            event_type: EventType::MessageSent,
            timestamp: Utc::now(),
            from_agent: agent_id,
            to_agent: neighbor_id,
            vector_clock: HashMap::new(),
            payload_size: 2048,
            duration_ms: 5,
        });

        timeline.record_event(TimelineEvent {
            event_id: format!("ack_{}_{}", agent_id, neighbor_id),
            event_type: EventType::AckSent,
            timestamp: Utc::now(),
            from_agent: neighbor_id,
            to_agent: agent_id,
            vector_clock: HashMap::new(),
            payload_size: 64,
            duration_ms: 1,
        });
    }

    timeline.finalize_metrics();

    // Step 8: Create dashboard and aggregate all data
    let mut dashboard = Dashboard::new("Full Pipeline Test".to_string());
    dashboard.update_from_orchestration(&orchestration);
    dashboard.update_from_timeline(&timeline);

    // Step 9: Verify complete pipeline
    assert_eq!(dashboard.network_data.total_agents, 9);
    assert_eq!(orchestration.current_round, 0); // No sync scheduled yet

    // Schedule sync
    let sync_result = orchestration.schedule_sync_round();
    assert!(sync_result.is_ok());
    assert_eq!(orchestration.current_round, 1);

    // Verify stats
    let stats = orchestration.get_round_stats();
    assert_eq!(stats.active_agents, 9);
    assert_eq!(stats.total_agents, 9);

    // Dashboard should show activity
    assert!(dashboard.performance_data.total_messages > 0);
    assert!(dashboard.timeline_data.total_events > 0);

    // Render outputs
    let html = dashboard.render_html();
    let json = dashboard.render_json();

    assert!(html.contains("Full Pipeline Test"));
    assert!(json.contains("\"active_agents\": 9"));
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 9: Failure Recovery
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_agent_failure_and_recovery() {
    let mut orchestration = OrchestrationState::new();

    // Register agents
    for i in 0..5 {
        orchestration
            .register_agent(i, vec![(i + 1) % 5])
            .unwrap();
    }

    assert_eq!(orchestration.get_active_agents().len(), 5);

    // Simulate timeout for agent 2
    orchestration.check_agent_health(1).unwrap(); // 1 second timeout

    // Agent 2 should be marked inactive after timeout
    if let Some(metadata) = orchestration.agents.get(&2) {
        assert_eq!(metadata.is_active, false);
    }

    // Deregister failed agent
    orchestration.deregister_agent(2).unwrap();

    // Verify removal
    assert_eq!(orchestration.agents.len(), 4);
    assert!(!orchestration.topology.contains_key(&2));

    // Remaining agents should still be active
    let active = orchestration.get_active_agents();
    assert_eq!(active.len(), 4);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test 10: Multi-Round Synchronization
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_multi_round_synchronization() {
    let mut orchestration = OrchestrationState::new();
    let mut timeline = InteractionTimeline::new(1000);

    // Register 3 agents
    for i in 0..3 {
        orchestration
            .register_agent(i, vec![(i + 1) % 3])
            .unwrap();
    }

    // Run 5 synchronization rounds
    for round in 1..=5 {
        // Schedule round
        orchestration.schedule_sync_round().unwrap();
        assert_eq!(orchestration.current_round, round);

        // Simulate round completion
        for agent_id in 0..3 {
            if let Some(metadata) = orchestration.agents.get_mut(&agent_id) {
                metadata.syncs_completed += 1;
                metadata.messages_processed += 10;
            }
        }

        // Record timeline events
        for agent_id in 0..3 {
            timeline.record_event(TimelineEvent {
                event_id: format!("sync_round_{}_{}", round, agent_id),
                event_type: EventType::SyncCompleted,
                timestamp: Utc::now(),
                from_agent: agent_id,
                to_agent: (agent_id + 1) % 3,
                vector_clock: HashMap::new(),
                payload_size: 512,
                duration_ms: 10,
            });
        }
    }

    timeline.finalize_metrics();

    // Verify all rounds completed
    assert_eq!(orchestration.current_round, 5);

    // Check stats
    let stats = orchestration.get_round_stats();
    assert_eq!(stats.round, 5);
    assert_eq!(stats.active_agents, 3);

    // Verify timeline captured all syncs
    assert_eq!(timeline.metrics.total_syncs, 5);
}
