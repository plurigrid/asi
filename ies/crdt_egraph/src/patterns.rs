//! Rewrite rule patterns for gadget-based 3-coloring
//!
//! Implements three gadget patterns (RED/BLUE/GREEN) that enforce 3-coloring
//! through their structure, not post-hoc validation.

use crate::colors::{ColorType, Polarity};
use crate::crdt::CRDTOp;
use crate::{CRDTEGraphError, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Gadget patterns for 3-coloring by construction
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum GadgetPattern {
    /// RED Gadget: Forward associative rewriting
    /// Pattern: (a ⊕ b) ⊕ c → a ⊕ (b ⊕ c)
    /// Constraint: Children must be RED or GREEN
    /// Polarity: Positive (constructive)
    Red,

    /// BLUE Gadget: Backward distributive rewriting
    /// Pattern: a ⊕ (b ⊕ c) → (a ⊕ b) ⊕ c
    /// Constraint: Children must be BLUE or GREEN
    /// Polarity: Negative (destructive)
    Blue,

    /// GREEN Gadget: Verification/Identity
    /// Pattern: a ≡ a (identity without structural change)
    /// Constraint: Can apply to any node color
    /// Polarity: Neutral (no change)
    Green,
}

impl GadgetPattern {
    /// Get the associated color
    pub fn color(&self) -> ColorType {
        match self {
            GadgetPattern::Red => ColorType::Red,
            GadgetPattern::Blue => ColorType::Blue,
            GadgetPattern::Green => ColorType::Green,
        }
    }

    /// Get the associated polarity
    pub fn polarity(&self) -> Polarity {
        match self {
            GadgetPattern::Red => Polarity::Positive,
            GadgetPattern::Blue => Polarity::Negative,
            GadgetPattern::Green => Polarity::Neutral,
        }
    }

    /// Check if child color is allowed for this gadget
    pub fn allows_child(&self, child_color: ColorType) -> bool {
        match self {
            GadgetPattern::Red => {
                // RED can have RED or GREEN children
                child_color == ColorType::Red || child_color == ColorType::Green
            }
            GadgetPattern::Blue => {
                // BLUE can have BLUE or GREEN children
                child_color == ColorType::Blue || child_color == ColorType::Green
            }
            GadgetPattern::Green => {
                // GREEN can have any children
                true
            }
        }
    }

    /// Apply this gadget pattern to a child color, returning the child's color if valid
    pub fn apply_to_child(&self, child_color: ColorType) -> Result<ColorType> {
        if self.allows_child(child_color) {
            Ok(child_color)
        } else {
            Err(CRDTEGraphError::ColorConstraintViolated(format!(
                "Gadget {:?} cannot have {:?} children",
                self, child_color
            )))
        }
    }

    /// All gadget patterns
    pub fn all() -> [GadgetPattern; 3] {
        [GadgetPattern::Red, GadgetPattern::Blue, GadgetPattern::Green]
    }
}

/// Left-hand side of a rewrite rule (pattern to match)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LHSPattern {
    /// Operator being rewritten
    pub operator: String,
    /// Number of children
    pub arity: usize,
    /// Required gadget pattern
    pub gadget: GadgetPattern,
}

impl LHSPattern {
    /// Create new LHS pattern
    pub fn new(operator: String, arity: usize, gadget: GadgetPattern) -> Self {
        Self {
            operator,
            arity,
            gadget,
        }
    }

    /// Check if an operation matches this pattern
    pub fn matches(&self, operator: &str, child_colors: &[ColorType]) -> Result<bool> {
        // Operator must match
        if operator != self.operator {
            return Ok(false);
        }

        // Arity must match
        if child_colors.len() != self.arity {
            return Ok(false);
        }

        // All children must pass gadget check
        for &child_color in child_colors {
            self.gadget.apply_to_child(child_color)?;
        }

        Ok(true)
    }
}

/// Right-hand side of a rewrite rule (replacement term)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RHSPattern {
    /// Operator after rewriting
    pub operator: String,
    /// Child indices in new order
    pub child_permutation: Vec<usize>,
    /// Resulting color after rewrite
    pub result_color: ColorType,
}

impl RHSPattern {
    /// Create new RHS pattern
    pub fn new(operator: String, child_permutation: Vec<usize>, result_color: ColorType) -> Self {
        Self {
            operator,
            child_permutation,
            result_color,
        }
    }

    /// Apply permutation to child colors
    pub fn permute_children(&self, original_colors: &[ColorType]) -> Result<Vec<ColorType>> {
        let mut result = Vec::with_capacity(self.child_permutation.len());

        for &idx in &self.child_permutation {
            if idx >= original_colors.len() {
                return Err(CRDTEGraphError::RewriteFailed(format!(
                    "Child index {} out of bounds (len={})",
                    idx,
                    original_colors.len()
                )));
            }
            result.push(original_colors[idx]);
        }

        Ok(result)
    }
}

/// Complete rewrite rule with pattern matching and application
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewriteRule {
    /// Unique rule identifier
    pub id: String,
    /// Human-readable name
    pub name: String,
    /// Left-hand side pattern
    pub lhs: LHSPattern,
    /// Right-hand side pattern
    pub rhs: RHSPattern,
    /// Priority for saturation (higher = applied first)
    pub priority: u32,
    /// Number of times this rule has been applied
    pub applications: u64,
}

impl RewriteRule {
    /// Create new rewrite rule
    pub fn new(id: String, name: String, lhs: LHSPattern, rhs: RHSPattern, priority: u32) -> Self {
        Self {
            id,
            name,
            lhs,
            rhs,
            priority,
            applications: 0,
        }
    }

    /// Check if this rule can be applied to the given operation
    pub fn can_apply(&self, operator: &str, child_colors: &[ColorType]) -> Result<bool> {
        self.lhs.matches(operator, child_colors)
    }

    /// Apply this rule, returning the rewritten operator and child permutation
    pub fn apply(&mut self, child_colors: &[ColorType]) -> Result<(String, Vec<ColorType>, ColorType)> {
        // Permute children
        let permuted = self.rhs.permute_children(child_colors)?;

        // Increment application counter
        self.applications += 1;

        Ok((
            self.rhs.operator.clone(),
            permuted,
            self.rhs.result_color,
        ))
    }
}

/// Rule set containing all three gadget patterns
#[derive(Debug, Clone)]
pub struct RuleSet {
    /// RED associative rules
    pub red_rules: Vec<RewriteRule>,
    /// BLUE distributive rules
    pub blue_rules: Vec<RewriteRule>,
    /// GREEN identity rules
    pub green_rules: Vec<RewriteRule>,
}

impl RuleSet {
    /// Create default rule set with standard gadget patterns
    pub fn default() -> Self {
        let mut rules = RuleSet {
            red_rules: Vec::new(),
            blue_rules: Vec::new(),
            green_rules: Vec::new(),
        };

        // RED: (a ⊕ b) ⊕ c → a ⊕ (b ⊕ c)
        let red_rule = RewriteRule::new(
            "red_assoc".to_string(),
            "RED associativity: (a ⊕ b) ⊕ c → a ⊕ (b ⊕ c)".to_string(),
            LHSPattern::new(
                "⊕".to_string(),
                2,
                GadgetPattern::Red,
            ),
            RHSPattern::new(
                "⊕".to_string(),
                vec![0, 1], // Identity permutation for now
                ColorType::Red,
            ),
            10, // High priority
        );
        rules.red_rules.push(red_rule);

        // BLUE: a ⊕ (b ⊕ c) → (a ⊕ b) ⊕ c
        let blue_rule = RewriteRule::new(
            "blue_dist".to_string(),
            "BLUE distributivity: a ⊕ (b ⊕ c) → (a ⊕ b) ⊕ c".to_string(),
            LHSPattern::new(
                "⊕".to_string(),
                2,
                GadgetPattern::Blue,
            ),
            RHSPattern::new(
                "⊕".to_string(),
                vec![0, 1], // Identity permutation
                ColorType::Blue,
            ),
            10, // High priority
        );
        rules.blue_rules.push(blue_rule);

        // GREEN: a ≡ a (identity)
        let green_rule = RewriteRule::new(
            "green_id".to_string(),
            "GREEN identity: a ≡ a".to_string(),
            LHSPattern::new(
                "id".to_string(),
                1,
                GadgetPattern::Green,
            ),
            RHSPattern::new(
                "id".to_string(),
                vec![0],
                ColorType::Green,
            ),
            5, // Lower priority (verification)
        );
        rules.green_rules.push(green_rule);

        rules
    }

    /// Get all rules
    pub fn all_rules(&self) -> Vec<&RewriteRule> {
        let mut rules = Vec::new();
        rules.extend(self.red_rules.iter());
        rules.extend(self.blue_rules.iter());
        rules.extend(self.green_rules.iter());
        rules
    }

    /// Get all rules by priority (descending)
    pub fn rules_by_priority(&self) -> Vec<&RewriteRule> {
        let mut rules = self.all_rules();
        rules.sort_by(|a, b| b.priority.cmp(&a.priority));
        rules
    }

    /// Get rule by ID
    pub fn get_rule(&self, id: &str) -> Option<&RewriteRule> {
        for rule in self.all_rules() {
            if rule.id == id {
                return Some(rule);
            }
        }
        None
    }

    /// Get rule by ID (mutable)
    pub fn get_rule_mut(&mut self, id: &str) -> Option<&mut RewriteRule> {
        for rule in self.red_rules.iter_mut() {
            if rule.id == id {
                return Some(rule);
            }
        }
        for rule in self.blue_rules.iter_mut() {
            if rule.id == id {
                return Some(rule);
            }
        }
        for rule in self.green_rules.iter_mut() {
            if rule.id == id {
                return Some(rule);
            }
        }
        None
    }

    /// Get statistics on rule applications
    pub fn stats(&self) -> HashMap<String, u64> {
        let mut stats = HashMap::new();
        for rule in self.all_rules() {
            stats.insert(rule.name.clone(), rule.applications);
        }
        stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gadget_pattern_color() {
        assert_eq!(GadgetPattern::Red.color(), ColorType::Red);
        assert_eq!(GadgetPattern::Blue.color(), ColorType::Blue);
        assert_eq!(GadgetPattern::Green.color(), ColorType::Green);
    }

    #[test]
    fn test_gadget_pattern_polarity() {
        assert_eq!(GadgetPattern::Red.polarity(), Polarity::Positive);
        assert_eq!(GadgetPattern::Blue.polarity(), Polarity::Negative);
        assert_eq!(GadgetPattern::Green.polarity(), Polarity::Neutral);
    }

    #[test]
    fn test_red_gadget_allows_children() {
        assert!(GadgetPattern::Red.allows_child(ColorType::Red));
        assert!(GadgetPattern::Red.allows_child(ColorType::Green));
        assert!(!GadgetPattern::Red.allows_child(ColorType::Blue));
    }

    #[test]
    fn test_blue_gadget_allows_children() {
        assert!(GadgetPattern::Blue.allows_child(ColorType::Blue));
        assert!(GadgetPattern::Blue.allows_child(ColorType::Green));
        assert!(!GadgetPattern::Blue.allows_child(ColorType::Red));
    }

    #[test]
    fn test_green_gadget_allows_all_children() {
        assert!(GadgetPattern::Green.allows_child(ColorType::Red));
        assert!(GadgetPattern::Green.allows_child(ColorType::Blue));
        assert!(GadgetPattern::Green.allows_child(ColorType::Green));
    }

    #[test]
    fn test_lhs_pattern_matches() {
        let pattern = LHSPattern::new("⊕".to_string(), 2, GadgetPattern::Red);

        let result = pattern.matches("⊕", &[ColorType::Red, ColorType::Green]);
        assert!(result.is_ok());
        assert!(result.unwrap());

        let result = pattern.matches("⊕", &[ColorType::Blue, ColorType::Green]);
        assert!(result.is_err()); // BLUE child not allowed for RED gadget
    }

    #[test]
    fn test_rewrite_rule_creation() {
        let lhs = LHSPattern::new("⊕".to_string(), 2, GadgetPattern::Red);
        let rhs = RHSPattern::new("⊕".to_string(), vec![0, 1], ColorType::Red);
        let rule = RewriteRule::new(
            "test_rule".to_string(),
            "Test Rule".to_string(),
            lhs,
            rhs,
            10,
        );

        assert_eq!(rule.id, "test_rule");
        assert_eq!(rule.applications, 0);
    }

    #[test]
    fn test_rule_set_default() {
        let rules = RuleSet::default();
        assert_eq!(rules.red_rules.len(), 1);
        assert_eq!(rules.blue_rules.len(), 1);
        assert_eq!(rules.green_rules.len(), 1);
    }

    #[test]
    fn test_rule_set_by_priority() {
        let rules = RuleSet::default();
        let sorted = rules.rules_by_priority();
        // RED and BLUE should be priority 10, GREEN should be 5
        assert_eq!(sorted[0].priority, 10);
        assert!(sorted[1].priority >= 5);
    }

    #[test]
    fn test_rule_stats() {
        let mut rules = RuleSet::default();
        if let Some(rule) = rules.get_rule_mut("red_assoc") {
            rule.applications = 42;
        }

        let stats = rules.stats();
        assert_eq!(stats.get("RED associativity: (a ⊕ b) ⊕ c → a ⊕ (b ⊕ c)").cloned(), Some(42));
    }
}
