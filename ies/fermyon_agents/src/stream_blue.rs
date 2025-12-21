/*!
    stream-blue: Negative/Backward Operations for CRDT E-Graph

    BLUE nodes represent negative/backward operations:
    - Destructive decomposition patterns
    - Cleaning up unnecessary structures
    - Polarity: Negative
    - Children must be BLUE or GREEN (never RED)

    Integration: Handles inverse operations and conflict resolution
    - Supports undo/rollback operations
    - Implements backfill phase in saturation
    - Coordinates with stream-red for state transitions
*/

use crate::{Color, ENode, CRDTEGraph};

/// BLUE node - negative/backward operations
#[derive(Debug, Clone)]
pub struct StreamBlue {
    pub operator: String,
    pub arity: usize,
    pub is_distributive: bool,
    pub priority: u32,
}

impl StreamBlue {
    pub fn new(operator: String, arity: usize, is_distributive: bool) -> Self {
        Self {
            operator,
            arity,
            is_distributive,
            priority: 10,
        }
    }

    /// Check if color constraint is satisfied for BLUE nodes
    pub fn verify_children_colors(child_colors: &[Color]) -> bool {
        // BLUE nodes can only have BLUE or GREEN children
        child_colors.iter().all(|c| *c == Color::Blue || *c == Color::Green)
    }

    /// Add BLUE node to e-graph with constraint checking
    pub fn add_to_egraph(egraph: &mut CRDTEGraph, operator: String, children: Vec<String>) -> Result<String, String> {
        // Check that children exist and have compatible colors
        for child_id in &children {
            if let Some(child_node) = egraph.nodes.get(child_id) {
                if child_node.color == Color::Red {
                    return Err(format!("BLUE nodes cannot have RED children ({})", child_id));
                }
            } else {
                return Err(format!("Child node not found: {}", child_id));
            }
        }

        // Create BLUE node
        let node = ENode::new(operator, children, Color::Blue);
        egraph.add_node(node)
    }

    /// Apply backward rewrite: decompose two BLUE nodes
    pub fn backward_rewrite(egraph: &mut CRDTEGraph, node1_id: String, node2_id: String) -> Result<(), String> {
        if !egraph.nodes.contains_key(&node1_id) {
            return Err(format!("Node not found: {}", node1_id));
        }
        if !egraph.nodes.contains_key(&node2_id) {
            return Err(format!("Node not found: {}", node2_id));
        }

        // Check color compatibility
        let node1_color = egraph.nodes.get(&node1_id).unwrap().color;
        let node2_color = egraph.nodes.get(&node2_id).unwrap().color;

        if node1_color == Color::Red || node2_color == Color::Red {
            return Err("Cannot rewrite with RED nodes".to_string());
        }

        // Perform decomposition
        if let (Some(class1), Some(class2)) = (
            egraph.node_to_class.get(&node1_id).cloned(),
            egraph.node_to_class.get(&node2_id).cloned(),
        ) {
            if class1 != class2 {
                // Separate classes
                egraph.node_to_class.insert(node2_id.clone(), class2);
            }
        }

        Ok(())
    }

    /// Extract BLUE gadget from e-graph
    pub fn extract_gadget(egraph: &CRDTEGraph, operator: &str) -> Option<String> {
        for (id, node) in &egraph.nodes {
            if node.operator == operator && node.color == Color::Blue {
                return Some(id.clone());
            }
        }
        None
    }

    /// Count BLUE nodes in e-graph
    pub fn count_blue_nodes(egraph: &CRDTEGraph) -> usize {
        egraph.nodes.values().filter(|n| n.color == Color::Blue).count()
    }

    /// Get all BLUE nodes
    pub fn get_blue_nodes(egraph: &CRDTEGraph) -> Vec<String> {
        egraph.nodes
            .iter()
            .filter(|(_, node)| node.color == Color::Blue)
            .map(|(id, _)| id.clone())
            .collect()
    }

    /// Create CRDT inverse operation
    pub fn create_inverse(operator: &str) -> String {
        format!("inv({})", operator)
    }

    /// Check if operation is invertible
    pub fn is_invertible(operator: &str) -> bool {
        !operator.contains("side_effect")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_children_colors() {
        assert!(StreamBlue::verify_children_colors(&[Color::Blue, Color::Green]));
        assert!(!StreamBlue::verify_children_colors(&[Color::Blue, Color::Red]));
        assert!(!StreamBlue::verify_children_colors(&[Color::Red]));
    }

    #[test]
    fn test_add_to_egraph() {
        let mut egraph = CRDTEGraph::new();

        // Add a GREEN base node
        let green_node = ENode::new("base".to_string(), vec![], Color::Green);
        let green_id = egraph.add_node(green_node).unwrap();

        // Add a BLUE node with the GREEN node as child
        let result = StreamBlue::add_to_egraph(&mut egraph, "distrib".to_string(), vec![green_id]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_create_inverse() {
        let inv = StreamBlue::create_inverse("append");
        assert_eq!(inv, "inv(append)");
    }

    #[test]
    fn test_count_blue_nodes() {
        let mut egraph = CRDTEGraph::new();
        let blue_node = ENode::new("op".to_string(), vec![], Color::Blue);
        egraph.add_node(blue_node).unwrap();

        assert_eq!(StreamBlue::count_blue_nodes(&egraph), 1);
    }
}
