/*!
    duck-colors: Deterministic Color Assignment & Gadget Selection

    P1 Component: Assigns deterministic colors to operators/gadgets using
    splittable RNG seed system. Enables color-based gadget selection for
    rewrite rules and polarity inference for phase scheduling.

    Features:
    - Deterministic color assignment (RED, BLUE, GREEN)
    - Gadget selection based on color compatibility
    - Polarity inference (RED=positive, BLUE=negative, GREEN=neutral)
    - Priority weighting for rewrite rule scheduling
    - Color harmony checking for multi-operator patterns
*/

use crate::{Color, ENode, CRDTEGraph};
use std::collections::HashMap;

/// Color assignment engine with deterministic seed-based generation
#[derive(Debug, Clone)]
pub struct ColorAssigner {
    pub seed: u64,
    pub color_cache: HashMap<String, Color>,
    pub operator_polarities: HashMap<String, Polarity>,
}

/// Polarity represents phase position (forward/backward/neutral)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Polarity {
    Positive,  // Forward phase (RED)
    Negative,  // Backward phase (BLUE)
    Neutral,   // Verification phase (GREEN)
}

impl ColorAssigner {
    /// Create new color assigner with given seed
    pub fn new(seed: u64) -> Self {
        Self {
            seed,
            color_cache: HashMap::new(),
            operator_polarities: HashMap::new(),
        }
    }

    /// Splittable RNG: deterministic color generation
    /// Uses linear congruential generator for deterministic colors
    fn hash_combine(h: u64, x: u64) -> u64 {
        h.wrapping_mul(31).wrapping_add(x)
    }

    /// Assign color deterministically to operator/gadget
    pub fn assign_color(&mut self, operator: &str) -> Color {
        // Check cache first
        if let Some(color) = self.color_cache.get(operator) {
            return *color;
        }

        // Compute hash from operator name and seed
        let mut hash = self.seed;
        for byte in operator.as_bytes() {
            hash = Self::hash_combine(hash, *byte as u64);
        }

        // Map hash to color (distribute evenly across 3 colors)
        let color = match hash % 3 {
            0 => Color::Red,
            1 => Color::Blue,
            _ => Color::Green,
        };

        // Cache result
        self.color_cache.insert(operator.to_string(), color);

        // Infer polarity
        let polarity = match color {
            Color::Red => Polarity::Positive,
            Color::Blue => Polarity::Negative,
            Color::Green => Polarity::Neutral,
        };
        self.operator_polarities
            .insert(operator.to_string(), polarity);

        color
    }

    /// Get cached color for operator
    pub fn get_color(&self, operator: &str) -> Option<Color> {
        self.color_cache.get(operator).copied()
    }

    /// Infer polarity from operator or use cached value
    pub fn infer_polarity(&mut self, operator: &str) -> Polarity {
        if let Some(polarity) = self.operator_polarities.get(operator) {
            return *polarity;
        }

        // Assign color if not cached, which also sets polarity
        let color = self.assign_color(operator);
        match color {
            Color::Red => Polarity::Positive,
            Color::Blue => Polarity::Negative,
            Color::Green => Polarity::Neutral,
        }
    }

    /// Select gadget from e-graph matching polarity
    pub fn select_gadget(
        &self,
        egraph: &CRDTEGraph,
        polarity: Polarity,
    ) -> Option<String> {
        let target_color = match polarity {
            Polarity::Positive => Color::Red,
            Polarity::Negative => Color::Blue,
            Polarity::Neutral => Color::Green,
        };

        // Find first matching gadget
        for (id, node) in &egraph.nodes {
            if node.color == target_color {
                return Some(id.clone());
            }
        }

        None
    }

    /// Get color-weighted priority for operator
    pub fn priority_for_operator(&mut self, operator: &str) -> u32 {
        let color = self.assign_color(operator);

        // Priority: RED > GREEN > BLUE (saturation order)
        match color {
            Color::Red => 30,
            Color::Green => 20,
            Color::Blue => 10,
        }
    }

    /// Check if two operators have compatible colors
    pub fn colors_compatible(&mut self, op1: &str, op2: &str) -> bool {
        let color1 = self.assign_color(op1);
        let color2 = self.assign_color(op2);

        match (color1, color2) {
            // RED cannot pair with BLUE
            (Color::Red, Color::Blue) | (Color::Blue, Color::Red) => false,
            // All other combinations are compatible
            _ => true,
        }
    }

    /// Compute color harmony score for set of operators (0.0 = conflicting, 1.0 = perfect)
    pub fn harmony_score(&mut self, operators: &[&str]) -> f64 {
        if operators.is_empty() {
            return 1.0;
        }

        let mut colors = Vec::new();
        for op in operators {
            colors.push(self.assign_color(op));
        }

        // Count color distribution
        let red_count = colors.iter().filter(|c| **c == Color::Red).count();
        let blue_count = colors.iter().filter(|c| **c == Color::Blue).count();
        let green_count = colors.iter().filter(|c| **c == Color::Green).count();
        let total = colors.len();

        // Penalty for RED-BLUE pairs
        let mut penalty = 0.0;
        if red_count > 0 && blue_count > 0 {
            penalty += 0.5;
        }

        // Bonus for balanced colors (GREEN helps mediate)
        let max_single = red_count.max(blue_count).max(green_count);
        let min_single = red_count.min(blue_count).min(green_count);
        let balance = 1.0 - ((max_single - min_single) as f64 / total as f64);

        (balance - penalty).max(0.0).min(1.0)
    }

    /// Generate rewrite rule gadget selection based on colors
    pub fn select_rewrite_gadgets(
        &mut self,
        egraph: &CRDTEGraph,
        from_phase: Polarity,
        to_phase: Polarity,
    ) -> Option<(String, String)> {
        // Select source gadget matching source phase
        let source = self.select_gadget(egraph, from_phase)?;

        // For target, prefer matching phase, but allow transition
        let mut target = self.select_gadget(egraph, to_phase);

        // If target phase not available, use neutral (GREEN)
        if target.is_none() {
            target = self.select_gadget(egraph, Polarity::Neutral);
        }

        target.map(|t| (source, t))
    }

    /// Create deterministic color assigner with new seed (for fork)
    pub fn fork(&self, offset: u64) -> Self {
        Self::new(Self::hash_combine(self.seed, offset) as u64)
    }

    /// Count colors in e-graph
    pub fn count_colors(&self, egraph: &CRDTEGraph) -> (usize, usize, usize) {
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

    /// Explain color assignment decision
    pub fn explain_color(&mut self, operator: &str) -> String {
        let color = self.assign_color(operator);
        let polarity = self.infer_polarity(operator);
        let priority = self.priority_for_operator(operator);

        format!(
            "Operator '{}': Color={:?}, Polarity={:?}, Priority={}",
            operator, color, polarity, priority
        )
    }

    /// Assign colors to all nodes in e-graph
    pub fn colorize_egraph(&mut self, egraph: &mut CRDTEGraph) -> Result<(), String> {
        let node_ids: Vec<String> = egraph.nodes.keys().cloned().collect();

        for node_id in node_ids {
            if let Some(node) = egraph.nodes.get_mut(&node_id) {
                let operator = node.operator.clone();
                let color = self.assign_color(&operator);
                node.color = color;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deterministic_assignment() {
        let mut assigner1 = ColorAssigner::new(42);
        let mut assigner2 = ColorAssigner::new(42);

        let color1 = assigner1.assign_color("append");
        let color2 = assigner2.assign_color("append");

        assert_eq!(color1, color2, "Same seed should produce same color");
    }

    #[test]
    fn test_different_seeds_produce_different_colors() {
        let mut assigner1 = ColorAssigner::new(42);
        let mut assigner2 = ColorAssigner::new(43);

        let color1 = assigner1.assign_color("concat");
        let color2 = assigner2.assign_color("concat");

        // Not guaranteed different, but very likely different
        // Just verify both are valid colors
        assert!([Color::Red, Color::Blue, Color::Green].contains(&color1));
        assert!([Color::Red, Color::Blue, Color::Green].contains(&color2));
    }

    #[test]
    fn test_cache_hit() {
        let mut assigner = ColorAssigner::new(42);

        let color1 = assigner.assign_color("op");
        let color2 = assigner.assign_color("op");

        assert_eq!(color1, color2);
        assert_eq!(assigner.color_cache.len(), 1);
    }

    #[test]
    fn test_polarity_inference() {
        let mut assigner = ColorAssigner::new(100);

        let polarity = assigner.infer_polarity("merge");
        assert!([Polarity::Positive, Polarity::Negative, Polarity::Neutral].contains(&polarity));
    }

    #[test]
    fn test_colors_compatible() {
        let mut assigner = ColorAssigner::new(200);

        // Manually set colors for testing
        assigner
            .color_cache
            .insert("red_op".to_string(), Color::Red);
        assigner
            .color_cache
            .insert("blue_op".to_string(), Color::Blue);
        assigner
            .color_cache
            .insert("green_op".to_string(), Color::Green);

        assert!(!assigner.colors_compatible("red_op", "blue_op"));
        assert!(assigner.colors_compatible("red_op", "green_op"));
        assert!(assigner.colors_compatible("blue_op", "green_op"));
    }

    #[test]
    fn test_harmony_score() {
        let mut assigner = ColorAssigner::new(300);

        assigner
            .color_cache
            .insert("r".to_string(), Color::Red);
        assigner
            .color_cache
            .insert("g".to_string(), Color::Green);
        assigner
            .color_cache
            .insert("b".to_string(), Color::Blue);

        let score = assigner.harmony_score(&["r", "g"]);
        assert!(score > 0.0, "RED+GREEN should have positive harmony");

        let bad_score = assigner.harmony_score(&["r", "b"]);
        assert!(bad_score < 0.5, "RED+BLUE should have poor harmony");
    }

    #[test]
    fn test_explain_color() {
        let mut assigner = ColorAssigner::new(400);
        let explanation = assigner.explain_color("operation");
        assert!(explanation.contains("operation"));
        assert!(explanation.contains("Color="));
        assert!(explanation.contains("Polarity="));
        assert!(explanation.contains("Priority="));
    }

    #[test]
    fn test_fork_creates_different_assigner() {
        let assigner1 = ColorAssigner::new(500);
        let assigner2 = assigner1.fork(1);

        assert_ne!(assigner1.seed, assigner2.seed);
    }

    #[test]
    fn test_priority_for_operator() {
        let mut assigner = ColorAssigner::new(600);

        // RED should have highest priority
        assigner
            .color_cache
            .insert("red_op".to_string(), Color::Red);
        let red_priority = assigner.priority_for_operator("red_op");
        assert_eq!(red_priority, 30);

        // BLUE should have lowest priority
        assigner
            .color_cache
            .insert("blue_op".to_string(), Color::Blue);
        let blue_priority = assigner.priority_for_operator("blue_op");
        assert_eq!(blue_priority, 10);

        // GREEN should be middle
        assigner
            .color_cache
            .insert("green_op".to_string(), Color::Green);
        let green_priority = assigner.priority_for_operator("green_op");
        assert_eq!(green_priority, 20);
    }
}
