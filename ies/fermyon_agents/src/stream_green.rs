/*!
    stream-green: Neutral/Identity Operations for CRDT E-Graph

    GREEN nodes represent neutral/identity operations:
    - Verification and validation patterns
    - Convergence checking
    - Polarity: Neutral
    - Children can be any color (RED, BLUE, or GREEN)

    Integration: Convergence verification across phases
    - Validates 3-coloring constraints
    - Verifies CRDT properties
    - Detects network convergence
*/

use crate::{Color, ENode, CRDTEGraph};

/// GREEN node - neutral/identity operations
#[derive(Debug, Clone)]
pub struct StreamGreen {
    pub operator: String,
    pub is_identity: bool,
    pub is_transitive: bool,
}

impl StreamGreen {
    pub fn new(operator: String, is_identity: bool) -> Self {
        Self {
            operator,
            is_identity,
            is_transitive: true,
        }
    }

    /// Check if color constraint is satisfied for GREEN nodes
    pub fn verify_children_colors(_child_colors: &[Color]) -> bool {
        // GREEN nodes can have children of any color
        true
    }

    /// Add GREEN node to e-graph
    pub fn add_to_egraph(egraph: &mut CRDTEGraph, operator: String, children: Vec<String>) -> Result<String, String> {
        // GREEN nodes don't have color restrictions
        let node = ENode::new(operator, children, Color::Green);
        egraph.add_node(node)
    }

    /// Verify 3-coloring constraints for entire e-graph
    pub fn verify_three_coloring(egraph: &CRDTEGraph) -> Result<(), String> {
        for (node_id, node) in &egraph.nodes {
            for child_id in &node.children {
                if let Some(child) = egraph.nodes.get(child_id) {
                    // Check: RED cannot have BLUE children
                    if node.color == Color::Red && child.color == Color::Blue {
                        return Err(format!(
                            "RED node {} cannot have BLUE child {}",
                            node_id, child_id
                        ));
                    }
                    // Check: BLUE cannot have RED children
                    if node.color == Color::Blue && child.color == Color::Red {
                        return Err(format!(
                            "BLUE node {} cannot have RED child {}",
                            node_id, child_id
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    /// Check color distribution
    pub fn color_distribution(egraph: &CRDTEGraph) -> (usize, usize, usize) {
        let mut red = 0;
        let mut blue = 0;
        let mut green = 0;

        for node in egraph.nodes.values() {
            match node.color {
                Color::Red => red += 1,
                Color::Blue => blue += 1,
                Color::Green => green += 1,
            }
        }

        (red, blue, green)
    }

    /// Check if e-graph has converged
    pub fn is_converged(egraph: &CRDTEGraph, tolerance: usize) -> bool {
        let (red, blue, green) = Self::color_distribution(egraph);

        // Convergence criteria: relatively balanced or GREEN-dominant
        let max_color = red.max(blue).max(green);
        let min_color = red.min(blue).min(green);

        max_color - min_color <= tolerance
    }

    /// Apply verification rewrite (identity operation)
    pub fn identity_rewrite(egraph: &mut CRDTEGraph, node_id: String) -> Result<(), String> {
        if !egraph.nodes.contains_key(&node_id) {
            return Err(format!("Node not found: {}", node_id));
        }

        // Identity operation: node maps to itself
        let class_id = egraph.node_to_class.get(&node_id).cloned();

        if let Some(class) = class_id {
            egraph.node_to_class.insert(node_id, class);
        }

        Ok(())
    }

    /// Count GREEN nodes in e-graph
    pub fn count_green_nodes(egraph: &CRDTEGraph) -> usize {
        egraph.nodes.values().filter(|n| n.color == Color::Green).count()
    }

    /// Get all GREEN nodes
    pub fn get_green_nodes(egraph: &CRDTEGraph) -> Vec<String> {
        egraph.nodes
            .iter()
            .filter(|(_, node)| node.color == Color::Green)
            .map(|(id, _)| id.clone())
            .collect()
    }

    /// Create equivalence witness
    pub fn create_witness(op1: &str, op2: &str) -> String {
        format!("eq({}, {})", op1, op2)
    }

    /// Generate convergence proof
    pub fn convergence_proof(egraph: &CRDTEGraph) -> String {
        let (red, blue, green) = Self::color_distribution(egraph);
        let total = red + blue + green;

        format!(
            "Convergence proof: RED={} ({:.1}%), BLUE={} ({:.1}%), GREEN={} ({:.1}%), Total={}",
            red,
            (red as f64 / total as f64) * 100.0,
            blue,
            (blue as f64 / total as f64) * 100.0,
            green,
            (green as f64 / total as f64) * 100.0,
            total
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_three_coloring() {
        let mut egraph = CRDTEGraph::new();

        // Valid: RED with GREEN child
        let green_node = ENode::new("base".to_string(), vec![], Color::Green);
        let green_id = egraph.add_node(green_node).unwrap();

        let red_node = ENode::new("assoc".to_string(), vec![green_id], Color::Red);
        egraph.add_node(red_node).unwrap();

        assert!(StreamGreen::verify_three_coloring(&egraph).is_ok());
    }

    #[test]
    fn test_invalid_coloring() {
        let mut egraph = CRDTEGraph::new();

        // Invalid: RED with BLUE child
        let blue_node = ENode::new("base".to_string(), vec![], Color::Blue);
        let blue_id = egraph.add_node(blue_node).unwrap();

        let red_node = ENode::new("bad".to_string(), vec![blue_id], Color::Red);
        let _ = egraph.add_node(red_node);

        assert!(StreamGreen::verify_three_coloring(&egraph).is_err());
    }

    #[test]
    fn test_color_distribution() {
        let mut egraph = CRDTEGraph::new();

        let red = ENode::new("r".to_string(), vec![], Color::Red);
        let blue = ENode::new("b".to_string(), vec![], Color::Blue);
        let green = ENode::new("g".to_string(), vec![], Color::Green);

        egraph.add_node(red).unwrap();
        egraph.add_node(blue).unwrap();
        egraph.add_node(green).unwrap();

        let (r, b, g) = StreamGreen::color_distribution(&egraph);
        assert_eq!((r, b, g), (1, 1, 1));
    }

    #[test]
    fn test_convergence_proof() {
        let egraph = CRDTEGraph::new();
        let proof = StreamGreen::convergence_proof(&egraph);
        assert!(proof.contains("Convergence proof"));
    }

    #[test]
    fn test_create_witness() {
        let witness = StreamGreen::create_witness("f", "g");
        assert_eq!(witness, "eq(f, g)");
    }
}
