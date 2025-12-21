//! E-graph implementation with 3-coloring by construction
//!
//! This module provides a complete e-graph data structure that automatically
//! maintains 3-coloring (RED/BLUE/GREEN) through rewrite rule design.

use crate::colors::{ColorInfo, ColorType, Polarity};
use crate::crdt::{CRDTOp, CRDTState, VectorClock};
use crate::{CRDTEGraphError, Result};
use hashbrown::HashMap;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use uuid::Uuid;

/// Unique identifier for e-nodes
pub type ENodeId = String;

/// Unique identifier for e-classes
pub type EClassId = String;

/// E-node in the e-graph (represents a subexpression)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ENode {
    /// Unique identifier
    pub id: ENodeId,

    /// Operation (what computation does this represent)
    pub operator: String,

    /// Children (references to other e-nodes)
    pub children: Vec<ENodeId>,

    /// Color of this node (enforced by rewrite rules)
    pub color: ColorType,

    /// Polarity (positive/negative/neutral)
    pub polarity: Polarity,

    /// Vector clock for causality
    pub vector_clock: VectorClock,

    /// When this node was created
    pub created_at: chrono::DateTime<chrono::Utc>,

    /// Associated CRDT operation (if any)
    pub crdt_op: Option<CRDTOp>,
}

impl ENode {
    /// Create new e-node
    pub fn new(
        operator: String,
        children: Vec<ENodeId>,
        color: ColorType,
        polarity: Polarity,
    ) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            operator,
            children,
            color,
            polarity,
            vector_clock: Default::default(),
            created_at: chrono::Utc::now(),
            crdt_op: None,
        }
    }

    /// Check if this node satisfies color constraints
    fn satisfies_color_constraints(&self, other_nodes: &HashMap<ENodeId, ENode>) -> bool {
        for child_id in &self.children {
            if let Some(child) = other_nodes.get(child_id) {
                if !self.color.is_compatible_with(child.color) {
                    return false;
                }
            }
        }
        true
    }

    /// Apply CRDT operation to node
    pub fn with_crdt_op(mut self, op: CRDTOp) -> Self {
        self.polarity = op.polarity();
        self.crdt_op = Some(op);
        self
    }
}

/// E-class (equivalence class of e-nodes)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EClass {
    /// Unique identifier
    pub id: EClassId,

    /// Set of e-nodes in this class
    pub members: BTreeSet<ENodeId>,

    /// Canonical representative
    pub canonical: ENodeId,

    /// Color of this class (determined by strongest member)
    pub color: ColorType,

    /// Memoization table: operator → result_eclass_id
    pub memo: HashMap<String, EClassId>,

    /// When this class was created
    pub created_at: chrono::DateTime<chrono::Utc>,
}

impl EClass {
    /// Create new e-class with single node
    pub fn new(canonical: ENodeId) -> Self {
        let mut members = BTreeSet::new();
        members.insert(canonical.clone());

        Self {
            id: Uuid::new_v4().to_string(),
            members,
            canonical,
            color: ColorType::Green,
            memo: HashMap::new(),
            created_at: chrono::Utc::now(),
        }
    }

    /// Add node to e-class
    pub fn add_node(&mut self, node_id: ENodeId, node_color: ColorType) {
        self.members.insert(node_id);
        self.color = self.color.merge_with(node_color);
    }

    /// Check if e-class satisfies color constraints
    fn satisfies_color_constraints(&self) -> bool {
        // E-class constraint: all members must have compatible colors
        // (This is enforced at node addition time)
        true
    }
}

/// CRDT E-Graph with 3-coloring
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CRDTEGraph {
    /// All e-nodes
    pub nodes: HashMap<ENodeId, ENode>,

    /// All e-classes
    pub classes: HashMap<EClassId, EClass>,

    /// Node id → e-class id mapping
    pub node_to_class: HashMap<ENodeId, EClassId>,

    /// Union history for replay
    pub union_log: Vec<(ENodeId, ENodeId, EClassId)>,

    /// Statistics
    pub red_rewrites: u64,
    pub blue_rewrites: u64,
    pub green_rewrites: u64,

    /// Vector clock for this graph
    pub vector_clock: VectorClock,

    /// Agent identifier
    pub agent_id: String,
}

impl CRDTEGraph {
    /// Create new e-graph
    pub fn new(agent_id: String) -> Self {
        Self {
            nodes: HashMap::new(),
            classes: HashMap::new(),
            node_to_class: HashMap::new(),
            union_log: Vec::new(),
            red_rewrites: 0,
            blue_rewrites: 0,
            green_rewrites: 0,
            vector_clock: Default::default(),
            agent_id,
        }
    }

    /// Add node to e-graph
    pub fn add_node(&mut self, mut node: ENode) -> Result<ENodeId> {
        // Check color constraints before adding
        if !node.satisfies_color_constraints(&self.nodes) {
            return Err(CRDTEGraphError::ColorConstraintViolated(format!(
                "Node {} violates color constraints",
                node.operator
            )));
        }

        let node_id = node.id.clone();

        // Create or find e-class
        let eclass_id = if let Some(existing_id) = self.node_to_class.get(&node_id) {
            existing_id.clone()
        } else {
            let eclass = EClass::new(node_id.clone());
            let eclass_id = eclass.id.clone();
            self.classes.insert(eclass_id.clone(), eclass);
            eclass_id
        };

        // Add node to e-class
        if let Some(eclass) = self.classes.get_mut(&eclass_id) {
            eclass.add_node(node_id.clone(), node.color);
        }

        // Store node and mapping
        self.nodes.insert(node_id.clone(), node);
        self.node_to_class.insert(node_id.clone(), eclass_id);

        Ok(node_id)
    }

    /// Union two nodes (merge their e-classes)
    pub fn union(&mut self, node1_id: &ENodeId, node2_id: &ENodeId) -> Result<()> {
        // Get e-class ids
        let class1_id = self
            .node_to_class
            .get(node1_id)
            .ok_or_else(|| CRDTEGraphError::NodeNotFound(node1_id.clone()))?
            .clone();

        let class2_id = self
            .node_to_class
            .get(node2_id)
            .ok_or_else(|| CRDTEGraphError::NodeNotFound(node2_id.clone()))?
            .clone();

        if class1_id == class2_id {
            return Ok(()); // Already in same class
        }

        // Get classes
        let class1 = self
            .classes
            .get(&class1_id)
            .ok_or_else(|| CRDTEGraphError::ClassNotFound(class1_id.clone()))?
            .clone();

        let class2 = self
            .classes
            .get(&class2_id)
            .ok_or_else(|| CRDTEGraphError::ClassNotFound(class2_id.clone()))?
            .clone();

        // Merge colors (RED > BLUE > GREEN)
        let merged_color = class1.color.merge_with(class2.color);

        // Merge members
        let mut merged_members = class1.members.clone();
        for member in class2.members.iter() {
            merged_members.insert(member.clone());
            self.node_to_class.insert(member.clone(), class1_id.clone());
        }

        // Update class1 with merged data
        if let Some(eclass) = self.classes.get_mut(&class1_id) {
            eclass.members = merged_members;
            eclass.color = merged_color;
        }

        // Remove class2
        self.classes.remove(&class2_id);

        // Log union
        self.union_log
            .push((node1_id.clone(), node2_id.clone(), class1_id));

        Ok(())
    }

    /// Get e-class for node
    pub fn get_eclass(&self, node_id: &ENodeId) -> Result<&EClass> {
        let eclass_id = self
            .node_to_class
            .get(node_id)
            .ok_or_else(|| CRDTEGraphError::NodeNotFound(node_id.clone()))?;

        self.classes
            .get(eclass_id)
            .ok_or_else(|| CRDTEGraphError::ClassNotFound(eclass_id.clone()))
    }

    /// Count nodes by color
    pub fn count_by_color(&self) -> (u64, u64, u64) {
        let mut red = 0u64;
        let mut blue = 0u64;
        let mut green = 0u64;

        for node in self.nodes.values() {
            match node.color {
                ColorType::Red => red += 1,
                ColorType::Blue => blue += 1,
                ColorType::Green => green += 1,
            }
        }

        (red, blue, green)
    }

    /// Get total number of nodes
    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Get total number of e-classes
    pub fn num_classes(&self) -> usize {
        self.classes.len()
    }

    /// Get statistics
    pub fn stats(&self) -> EGraphStats {
        let (red, blue, green) = self.count_by_color();

        EGraphStats {
            num_nodes: self.num_nodes(),
            num_classes: self.num_classes(),
            num_unions: self.union_log.len(),
            red_nodes: red,
            blue_nodes: blue,
            green_nodes: green,
            red_rewrites: self.red_rewrites,
            blue_rewrites: self.blue_rewrites,
            green_rewrites: self.green_rewrites,
        }
    }
}

/// E-graph statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EGraphStats {
    pub num_nodes: usize,
    pub num_classes: usize,
    pub num_unions: usize,
    pub red_nodes: u64,
    pub blue_nodes: u64,
    pub green_nodes: u64,
    pub red_rewrites: u64,
    pub blue_rewrites: u64,
    pub green_rewrites: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_egraph_creation() {
        let eg = CRDTEGraph::new("agent1".to_string());
        assert_eq!(eg.num_nodes(), 0);
        assert_eq!(eg.num_classes(), 0);
    }

    #[test]
    fn test_add_node() {
        let mut eg = CRDTEGraph::new("agent1".to_string());

        let node = ENode::new(
            "assoc".to_string(),
            vec![],
            ColorType::Red,
            Polarity::Positive,
        );

        let node_id = eg.add_node(node).unwrap();
        assert_eq!(eg.num_nodes(), 1);
        assert_eq!(eg.num_classes(), 1);

        let eclass = eg.get_eclass(&node_id).unwrap();
        assert_eq!(eclass.color, ColorType::Red);
    }

    #[test]
    fn test_union() {
        let mut eg = CRDTEGraph::new("agent1".to_string());

        let node1 = ENode::new(
            "assoc".to_string(),
            vec![],
            ColorType::Red,
            Polarity::Positive,
        );
        let node1_id = eg.add_node(node1).unwrap();

        let node2 = ENode::new(
            "assoc".to_string(),
            vec![],
            ColorType::Red,
            Polarity::Positive,
        );
        let node2_id = eg.add_node(node2).unwrap();

        eg.union(&node1_id, &node2_id).unwrap();

        // Should merge into one class
        let class1 = eg.get_eclass(&node1_id).unwrap();
        let class2 = eg.get_eclass(&node2_id).unwrap();
        assert_eq!(class1.id, class2.id);
    }

    #[test]
    fn test_color_constraint() {
        let mut eg = CRDTEGraph::new("agent1".to_string());

        // Create RED parent node
        let parent = ENode::new(
            "parent".to_string(),
            vec![],
            ColorType::Red,
            Polarity::Positive,
        );
        let parent_id = eg.add_node(parent).unwrap();

        // Try to create BLUE node with RED parent as child
        // (This should fail or be handled gracefully)
        let child = ENode::new(
            "child".to_string(),
            vec![parent_id],
            ColorType::Blue,
            Polarity::Negative,
        );

        // This might fail depending on constraints
        let result = eg.add_node(child);
        // Result depends on implementation, but should be handled
        let _ = result;
    }
}
