/*!
    stream-red: Positive/Forward Operations for CRDT E-Graph

    RED nodes represent forward/constructive operations:
    - Associative rewriting patterns
    - Building up complex structures from primitives
    - Polarity: Positive
    - Children must be RED or GREEN (never BLUE)

    Integration: Phase 3A → Phase 3C
    - Extends distributed agent network to serverless
    - Provides color-based gadget selection
    - Implements skill derivation for Phases 2B-3C
*/

use crate::{Color, ENode, CRDTEGraph};

/// RED node - forward/constructive operations
#[derive(Debug, Clone)]
pub struct StreamRed {
    pub operator: String,
    pub arity: usize,
    pub is_associative: bool,
    pub priority: u32,
}

impl StreamRed {
    pub fn new(operator: String, arity: usize, is_associative: bool) -> Self {
        Self {
            operator,
            arity,
            is_associative,
            priority: 10,
        }
    }

    /// Check if color constraint is satisfied for RED nodes
    pub fn verify_children_colors(child_colors: &[Color]) -> bool {
        // RED nodes can only have RED or GREEN children
        child_colors.iter().all(|c| *c == Color::Red || *c == Color::Green)
    }

    /// Add RED node to e-graph with constraint checking
    pub fn add_to_egraph(egraph: &mut CRDTEGraph, operator: String, children: Vec<String>) -> Result<String, String> {
        // Check that children exist and have compatible colors
        for child_id in &children {
            if let Some(child_node) = egraph.nodes.get(child_id) {
                if child_node.color == Color::Blue {
                    return Err(format!("RED nodes cannot have BLUE children ({})", child_id));
                }
            } else {
                return Err(format!("Child node not found: {}", child_id));
            }
        }

        // Create RED node
        let node = ENode::new(operator, children, Color::Red);
        egraph.add_node(node)
    }

    /// Apply forward rewrite: combine two RED nodes
    pub fn forward_rewrite(egraph: &mut CRDTEGraph, node1_id: String, node2_id: String) -> Result<(), String> {
        if !egraph.nodes.contains_key(&node1_id) {
            return Err(format!("Node not found: {}", node1_id));
        }
        if !egraph.nodes.contains_key(&node2_id) {
            return Err(format!("Node not found: {}", node2_id));
        }

        // Merge nodes if they have compatible colors
        let node1_color = egraph.nodes.get(&node1_id).unwrap().color;
        let node2_color = egraph.nodes.get(&node2_id).unwrap().color;

        if node1_color == Color::Blue || node2_color == Color::Blue {
            return Err("Cannot rewrite with BLUE nodes".to_string());
        }

        // Perform union operation
        if let (Some(class1), Some(class2)) = (
            egraph.node_to_class.get(&node1_id).cloned(),
            egraph.node_to_class.get(&node2_id).cloned(),
        ) {
            if class1 != class2 {
                // Merge classes
                egraph.node_to_class.insert(node2_id.clone(), class1.clone());
            }
        }

        Ok(())
    }

    /// Extract RED gadget from e-graph
    pub fn extract_gadget(egraph: &CRDTEGraph, operator: &str) -> Option<String> {
        for (id, node) in &egraph.nodes {
            if node.operator == operator && node.color == Color::Red {
                return Some(id.clone());
            }
        }
        None
    }

    /// Count RED nodes in e-graph
    pub fn count_red_nodes(egraph: &CRDTEGraph) -> usize {
        egraph.nodes.values().filter(|n| n.color == Color::Red).count()
    }

    /// Get all RED nodes
    pub fn get_red_nodes(egraph: &CRDTEGraph) -> Vec<String> {
        egraph.nodes
            .iter()
            .filter(|(_, node)| node.color == Color::Red)
            .map(|(id, _)| id.clone())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_children_colors() {
        assert!(StreamRed::verify_children_colors(&[Color::Red, Color::Green]));
        assert!(!StreamRed::verify_children_colors(&[Color::Red, Color::Blue]));
        assert!(!StreamRed::verify_children_colors(&[Color::Blue]));
    }

    #[test]
    fn test_add_to_egraph() {
        let mut egraph = CRDTEGraph::new();

        // Add a GREEN base node
        let green_node = ENode::new("base".to_string(), vec![], Color::Green);
        let green_id = egraph.add_node(green_node).unwrap();

        // Add a RED node with the GREEN node as child
        let result = StreamRed::add_to_egraph(&mut egraph, "assoc".to_string(), vec![green_id]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_count_red_nodes() {
        let mut egraph = CRDTEGraph::new();
        let red_node = ENode::new("op".to_string(), vec![], Color::Red);
        egraph.add_node(red_node).unwrap();

        assert_eq!(StreamRed::count_red_nodes(&egraph), 1);
    }
}
