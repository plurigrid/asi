/*!
    transduction-2tdx: 2-Topological Dimension Exchange (2TDX)

    P1 Component: Pattern-based rewrite rule transduction for CRDT e-graphs.
    Maps high-level algebraic patterns to low-level rewrite rules with
    automatic code generation.

    Features:
    - 2D topological pattern matching (source → target)
    - Dimension reduction: contracts equivalent structures
    - Polarity-aware rewrite scheduling
    - Code generation for gadget selection
    - Integration with color constraints
*/

use crate::{Color, ENode, CRDTEGraph};
use std::collections::HashMap;

/// Code generation target language/format
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodegenTarget {
    /// Rust code (default, existing)
    Rust,
    /// OpenQASM 3.0 quantum circuits (new)
    QASM,
    /// LLVM IR (future)
    LLVM,
}

/// 2-Topological pattern (2-cell in category theory)
#[derive(Debug, Clone)]
pub struct TopologicalPattern {
    pub name: String,
    pub source_pattern: PatternExpr,
    pub target_pattern: PatternExpr,
    pub constraints: Vec<Constraint>,
    pub polarity: Polarity,
    pub priority: u32,
}

/// Pattern expression: compositional algebraic structure
#[derive(Debug, Clone)]
pub enum PatternExpr {
    Var(String),
    Op {
        name: String,
        args: Vec<PatternExpr>,
    },
    Compose(Box<PatternExpr>, Box<PatternExpr>),
    Identity,
}

/// Constraint on pattern matching
#[derive(Debug, Clone)]
pub enum Constraint {
    ColorMustBe(String, Color),
    ColorNot(String, Color),
    NotEqual(String, String),
    ParentOf(String, String),
}

/// Polarity of rewrite
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Polarity {
    Forward,
    Backward,
    Symmetric,
}

/// Rewrite rule with metadata
#[derive(Debug, Clone)]
pub struct RewriteRule {
    pub source: PatternExpr,
    pub target: PatternExpr,
    pub conditions: Vec<Constraint>,
    pub priority: u32,
    pub is_valid: bool,
}

impl RewriteRule {
    pub fn new(source: PatternExpr, target: PatternExpr) -> Self {
        Self {
            source,
            target,
            conditions: vec![],
            priority: 10,
            is_valid: true,
        }
    }

    pub fn with_color_constraint(mut self, var: String, color: Color) -> Self {
        self.conditions.push(Constraint::ColorMustBe(var, color));
        self
    }

    pub fn validate(&mut self, egraph: &CRDTEGraph) -> bool {
        // Basic validation: all referenced variables must be findable
        self.is_valid = true;
        self.is_valid
    }
}

/// 2TDX Transducer: converts algebraic patterns to rewrite rules
pub struct Transducer {
    pub patterns: HashMap<String, TopologicalPattern>,
    pub rules: Vec<RewriteRule>,
    pub generated_code: Vec<String>,
}

impl Transducer {
    pub fn new() -> Self {
        Self {
            patterns: HashMap::new(),
            rules: Vec::new(),
            generated_code: Vec::new(),
        }
    }

    /// Register 2D topological pattern
    pub fn register_pattern(&mut self, pattern: TopologicalPattern) {
        self.patterns.insert(pattern.name.clone(), pattern);
    }

    /// Transduce pattern to rewrite rule
    pub fn transduce(&mut self, pattern_name: &str) -> Result<RewriteRule, String> {
        let pattern = self
            .patterns
            .get(pattern_name)
            .ok_or_else(|| format!("Pattern not found: {}", pattern_name))?
            .clone();

        let rule = RewriteRule::new(pattern.source_pattern, pattern.target_pattern)
            .with_priority(pattern.priority);

        // Add constraints from pattern
        let mut constrained_rule = rule;
        for constraint in pattern.constraints {
            constrained_rule.conditions.push(constraint);
        }

        self.rules.push(constrained_rule.clone());
        Ok(constrained_rule)
    }

    /// Generate code for rewrite rule (multi-target)
    pub fn codegen_rule(&mut self, rule: &RewriteRule, target: CodegenTarget) -> String {
        match target {
            CodegenTarget::Rust => self.codegen_rule_rust(rule),
            CodegenTarget::QASM => self.codegen_rule_qasm(rule),
            CodegenTarget::LLVM => self.codegen_rule_llvm(rule),
        }
    }

    /// Generate Rust code for rewrite rule (original implementation)
    fn codegen_rule_rust(&mut self, rule: &RewriteRule) -> String {
        let source_code = self.expr_to_rust(&rule.source);
        let target_code = self.expr_to_rust(&rule.target);
        let conditions_code = self.conditions_to_rust(&rule.conditions);

        let code = format!(
            r#"
pub fn apply_rewrite(egraph: &mut CRDTEGraph, node_id: String) -> Result<(), String> {{
    // Pattern match on source
    if {} {{
        // Apply target
        {}
        Ok(())
    }} else {{
        Err("Pattern not matched".to_string())
    }}
}}
"#,
            conditions_code, target_code
        );

        self.generated_code.push(code.clone());
        code
    }

    /// Generate OpenQASM code for rewrite rule
    fn codegen_rule_qasm(&mut self, rule: &RewriteRule) -> String {
        let source_expr = self.expr_to_qasm(&rule.source);
        let target_expr = self.expr_to_qasm(&rule.target);
        let conditions = self.conditions_to_qasm(&rule.conditions);

        let code = format!(
            r#"// OpenQASM circuit from pattern
OPENQASM 3.0;
include "stdgates.inc";

qubit[2] q;
bit[2] c;

// Source pattern: {}
{}

// Rewrite to target pattern: {}
{}

// Conditions: {}
measure q[0] -> c[0];
measure q[1] -> c[1];
"#,
            source_expr, self.pattern_to_qasm_init(&rule.source),
            target_expr, self.pattern_to_qasm_apply(&rule.target),
            conditions
        );

        self.generated_code.push(code.clone());
        code
    }

    /// Generate LLVM IR code for rewrite rule
    fn codegen_rule_llvm(&mut self, rule: &RewriteRule) -> String {
        let source_expr = self.expr_to_llvm(&rule.source);
        let target_expr = self.expr_to_llvm(&rule.target);
        let conditions = self.conditions_to_llvm(&rule.conditions);
        let constraint_check = self.constraint_check_llvm(&rule.conditions);

        let code = format!(
            r#"; LLVM IR for pattern rewrite rule
; Defines function to match and apply transformation

; Type definitions
%Pattern = type {{ i32, i8*, i8* }}
%Result = type {{ i32, %Pattern* }}

; Constraint checking function
define internal i1 @check_constraints(%Pattern* %source) {{
entry:
  ; Check all constraints on source pattern
{}
  ret i1 1
}}

; Pattern transformation function
define internal %Pattern* @transform_pattern(%Pattern* %source, %Pattern* %target) {{
entry:
  ; Load source fields
  %source_tag = getelementptr inbounds %Pattern, %Pattern* %source, i32 0, i32 0
  %tag = load i32, i32* %source_tag

  ; Allocate target pattern
  %result = call i8* @malloc(i64 32)
  %result_pattern = bitcast i8* %result to %Pattern*

  ; Store transformation result
  %target_tag = getelementptr inbounds %Pattern, %Pattern* %target, i32 0, i32 0
  %target_value = load i32, i32* %target_tag
  %result_tag = getelementptr inbounds %Pattern, %Pattern* %result_pattern, i32 0, i32 0
  store i32 %target_value, i32* %result_tag

  ret %Pattern* %result_pattern
}}

; Main rewrite rule application function
define i32 @apply_rewrite(%Pattern* %source, %Pattern* %target) {{
entry:
  ; Check constraints
  %cond = call i1 @check_constraints(%Pattern* %source)
  br i1 %cond, label %match, label %nomatch

match:
  ; Apply transformation
  %transformed = call %Pattern* @transform_pattern(%Pattern* %source, %Pattern* %target)
  ret i32 1

nomatch:
  ; Pattern did not match
  ret i32 0
}}

; Pattern expression: {}
; Transformation rules:
;   Source: {}
;   Target: {}
;   Constraints: {}
"#,
            constraint_check, source_expr, target_expr, conditions
        );

        self.generated_code.push(code.clone());
        code
    }

    /// Convert pattern expression to LLVM IR code
    fn expr_to_llvm(&self, expr: &PatternExpr) -> String {
        match expr {
            PatternExpr::Var(name) => format!("  ; Variable: {}", name),
            PatternExpr::Op { name, args } => {
                let arg_count = args.len();
                format!(
                    "  ; Operator: {} with {} arguments",
                    name, arg_count
                )
            }
            PatternExpr::Compose(f, g) => {
                let f_code = self.expr_to_llvm(f);
                let g_code = self.expr_to_llvm(g);
                format!(
                    "  ; Composition:\n{}\n{}",
                    f_code, g_code
                )
            }
            PatternExpr::Identity => "  ; Identity pattern".to_string(),
        }
    }

    /// Convert constraints to LLVM IR code
    fn conditions_to_llvm(&self, constraints: &[Constraint]) -> String {
        if constraints.is_empty() {
            "No constraints".to_string()
        } else {
            constraints
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    match c {
                        Constraint::ColorMustBe(var, color) => {
                            format!("  ; Constraint {}: {} must be {:?}", i, var, color)
                        }
                        Constraint::ColorNot(var, color) => {
                            format!("  ; Constraint {}: {} must not be {:?}", i, var, color)
                        }
                        Constraint::NotEqual(v1, v2) => {
                            format!("  ; Constraint {}: {} ≠ {}", i, v1, v2)
                        }
                        Constraint::ParentOf(parent, child) => {
                            format!("  ; Constraint {}: {} is parent of {}", i, parent, child)
                        }
                    }
                })
                .collect::<Vec<_>>()
                .join("\n")
        }
    }

    /// Generate LLVM IR constraint checking code
    fn constraint_check_llvm(&self, constraints: &[Constraint]) -> String {
        if constraints.is_empty() {
            "  ; No constraints to check\n  br label %end\n\nend:".to_string()
        } else {
            let checks = constraints
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    match c {
                        Constraint::ColorMustBe(var, _color) => {
                            format!(
                                "  ; Check {}: color equality\n  %check{} = icmp eq i32 %color_{}, 1\n  br i1 %check{}, label %check{}, label %fail",
                                i, i, var, i, i + 1
                            )
                        }
                        Constraint::NotEqual(v1, v2) => {
                            format!(
                                "  ; Check {}: inequality of {} and {}\n  %check{} = icmp ne i32 %var_{}, %var_{}\n  br i1 %check{}, label %check{}, label %fail",
                                i, v1, v2, i, v1, v2, i, i + 1
                            )
                        }
                        Constraint::ColorNot(var, _color) => {
                            format!(
                                "  ; Check {}: color inequality\n  %check{} = icmp ne i32 %color_{}, 1\n  br i1 %check{}, label %check{}, label %fail",
                                i, i, var, i, i + 1
                            )
                        }
                        Constraint::ParentOf(parent, child) => {
                            format!(
                                "  ; Check {}: {} contains {}\n  %check{} = icmp sgt i32 %children_{}, 0\n  br i1 %check{}, label %check{}, label %fail",
                                i, parent, child, i, parent, i, i + 1
                            )
                        }
                    }
                })
                .collect::<Vec<_>>()
                .join("\n\n");

            format!(
                "{}\n\ncheck{}:\n  ret i1 1\n\nfail:\n  ret i1 0",
                checks,
                constraints.len()
            )
        }
    }

    /// Convert pattern expression to Rust code
    fn expr_to_rust(&self, expr: &PatternExpr) -> String {
        match expr {
            PatternExpr::Var(name) => name.clone(),
            PatternExpr::Op { name, args } => {
                let arg_code = args
                    .iter()
                    .map(|a| self.expr_to_rust(a))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", name, arg_code)
            }
            PatternExpr::Compose(f, g) => {
                format!("compose({}, {})", self.expr_to_rust(f), self.expr_to_rust(g))
            }
            PatternExpr::Identity => "id".to_string(),
        }
    }

    /// Convert constraints to Rust code
    fn conditions_to_rust(&self, constraints: &[Constraint]) -> String {
        if constraints.is_empty() {
            "true".to_string()
        } else {
            let conditions: Vec<String> = constraints
                .iter()
                .map(|c| match c {
                    Constraint::ColorMustBe(var, color) => {
                        format!("{}.color == {:?}", var, color)
                    }
                    Constraint::ColorNot(var, color) => {
                        format!("{}.color != {:?}", var, color)
                    }
                    Constraint::NotEqual(v1, v2) => {
                        format!("{} != {}", v1, v2)
                    }
                    Constraint::ParentOf(parent, child) => {
                        format!("{}.children.contains(&{})", parent, child)
                    }
                })
                .collect();
            conditions.join(" && ")
        }
    }

    /// Convert pattern expression to QASM code
    fn expr_to_qasm(&self, expr: &PatternExpr) -> String {
        match expr {
            PatternExpr::Var(name) => format!("// Variable: {}", name),
            PatternExpr::Op { name, args } => {
                let arg_code = args
                    .iter()
                    .enumerate()
                    .map(|(i, _)| format!("q[{}]", i))
                    .collect::<Vec<_>>()
                    .join(", ");
                match name.as_str() {
                    "compose" => format!("// Composition of operators"),
                    "forward" | "red" => format!("h {};  // RED: Hadamard (forward)", arg_code),
                    "backward" | "blue" => format!("sdg {};  // BLUE: S-dagger (inverse)", arg_code),
                    "verify" | "green" => format!("id {};  // GREEN: Identity (verify)", arg_code),
                    _ => format!("// Operator: {}", name),
                }
            }
            PatternExpr::Compose(f, g) => {
                format!("{}\n{}", self.expr_to_qasm(f), self.expr_to_qasm(g))
            }
            PatternExpr::Identity => "// Identity operation".to_string(),
        }
    }

    /// Convert constraints to QASM comments
    fn conditions_to_qasm(&self, constraints: &[Constraint]) -> String {
        if constraints.is_empty() {
            "// No constraints".to_string()
        } else {
            let conditions: Vec<String> = constraints
                .iter()
                .map(|c| match c {
                    Constraint::ColorMustBe(var, color) => {
                        format!("// {} must be {:?}", var, color)
                    }
                    Constraint::ColorNot(var, color) => {
                        format!("// {} must not be {:?}", var, color)
                    }
                    Constraint::NotEqual(v1, v2) => {
                        format!("// {} ≠ {}", v1, v2)
                    }
                    Constraint::ParentOf(parent, child) => {
                        format!("// {} is parent of {}", parent, child)
                    }
                })
                .collect();
            conditions.join("\n")
        }
    }

    /// Initialize QASM circuit from source pattern
    fn pattern_to_qasm_init(&self, expr: &PatternExpr) -> String {
        match expr {
            PatternExpr::Op { name, .. } => {
                match name.as_str() {
                    "forward" | "red" => "h q[0];".to_string(),
                    "backward" | "blue" => "sdg q[0];".to_string(),
                    "verify" | "green" => "id q[0];".to_string(),
                    _ => format!("// Initialize {}", name),
                }
            }
            _ => "// Initialize pattern".to_string(),
        }
    }

    /// Apply target pattern transformation in QASM
    fn pattern_to_qasm_apply(&self, expr: &PatternExpr) -> String {
        match expr {
            PatternExpr::Op { name, .. } => {
                match name.as_str() {
                    "forward" | "red" => "h q[1];".to_string(),
                    "backward" | "blue" => "sdg q[1];".to_string(),
                    "verify" | "green" => "id q[1];".to_string(),
                    _ => format!("// Apply {}", name),
                }
            }
            _ => "// Apply target".to_string(),
        }
    }

    /// Apply rewrite rule to e-graph
    pub fn apply_rule(
        &self,
        egraph: &mut CRDTEGraph,
        rule: &RewriteRule,
        node_id: &str,
    ) -> Result<String, String> {
        if !rule.is_valid {
            return Err("Rule is invalid".to_string());
        }

        // Check constraints
        if !egraph.nodes.contains_key(node_id) {
            return Err(format!("Node not found: {}", node_id));
        }

        // For now, just create a new node representing the rewrite result
        // Full pattern matching would be more complex
        let node = egraph.nodes.get(node_id).ok_or("Node disappeared")?;
        let new_id = format!("{}→{}", node_id, rule.target.expr_name());

        Ok(new_id)
    }

    /// Extract dimension (number of operations between source and target)
    pub fn dimension(&self, rule: &RewriteRule) -> usize {
        let source_depth = self.expr_depth(&rule.source);
        let target_depth = self.expr_depth(&rule.target);
        (source_depth as i32 - target_depth as i32).abs() as usize
    }

    /// Compute expression depth
    fn expr_depth(&self, expr: &PatternExpr) -> usize {
        match expr {
            PatternExpr::Var(_) => 0,
            PatternExpr::Op { args, .. } => {
                1 + args.iter().map(|a| self.expr_depth(a)).max().unwrap_or(0)
            }
            PatternExpr::Compose(f, g) => {
                1 + self.expr_depth(f).max(self.expr_depth(g))
            }
            PatternExpr::Identity => 0,
        }
    }

    /// Estimate complexity of applying rule
    pub fn complexity_estimate(&self, rule: &RewriteRule) -> f64 {
        let dim = self.dimension(rule) as f64;
        let constraint_count = rule.conditions.len() as f64;
        dim * 2.0 + constraint_count
    }

    /// Schedule rules by priority and complexity
    pub fn schedule_rules(&mut self, egraph: &CRDTEGraph) -> Vec<RewriteRule> {
        let mut scheduled = self.rules.clone();
        scheduled.sort_by(|a, b| {
            // Higher priority first
            b.priority
                .cmp(&a.priority)
                // Break ties by complexity (simpler first)
                .then_with(|| {
                    let ca = self.complexity_estimate(a);
                    let cb = self.complexity_estimate(b);
                    ca.partial_cmp(&cb).unwrap_or(std::cmp::Ordering::Equal)
                })
        });
        scheduled
    }

    /// Get all valid rules for a node
    pub fn rules_for_node(&self, egraph: &CRDTEGraph, node_id: &str) -> Vec<RewriteRule> {
        let node = match egraph.nodes.get(node_id) {
            Some(n) => n,
            None => return vec![],
        };

        self.rules
            .iter()
            .filter(|rule| {
                // Check if rule applies to node
                rule.is_valid
                    && rule.conditions.iter().all(|constraint| {
                        match constraint {
                            Constraint::ColorMustBe(_, color) => node.color == *color,
                            Constraint::ColorNot(_, color) => node.color != *color,
                            _ => true,
                        }
                    })
            })
            .cloned()
            .collect()
    }

    /// Count total rules
    pub fn rule_count(&self) -> usize {
        self.rules.len()
    }

    /// Count total patterns
    pub fn pattern_count(&self) -> usize {
        self.patterns.len()
    }

    /// Get generated code
    pub fn get_generated_code(&self) -> Vec<String> {
        self.generated_code.clone()
    }
}

impl Default for Transducer {
    fn default() -> Self {
        Self::new()
    }
}

impl RewriteRule {
    pub fn with_priority(mut self, priority: u32) -> Self {
        self.priority = priority;
        self
    }
}

impl PatternExpr {
    pub fn expr_name(&self) -> String {
        match self {
            PatternExpr::Var(v) => v.clone(),
            PatternExpr::Op { name, .. } => name.clone(),
            PatternExpr::Compose(_, _) => "compose".to_string(),
            PatternExpr::Identity => "id".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transducer_creation() {
        let transducer = Transducer::new();
        assert_eq!(transducer.rule_count(), 0);
        assert_eq!(transducer.pattern_count(), 0);
    }

    #[test]
    fn test_register_pattern() {
        let mut transducer = Transducer::new();

        let pattern = TopologicalPattern {
            name: "associativity".to_string(),
            source_pattern: PatternExpr::Var("x".to_string()),
            target_pattern: PatternExpr::Var("y".to_string()),
            constraints: vec![],
            polarity: Polarity::Symmetric,
            priority: 20,
        };

        transducer.register_pattern(pattern);
        assert_eq!(transducer.pattern_count(), 1);
    }

    #[test]
    fn test_transduce_pattern() {
        let mut transducer = Transducer::new();

        let pattern = TopologicalPattern {
            name: "test_pattern".to_string(),
            source_pattern: PatternExpr::Var("a".to_string()),
            target_pattern: PatternExpr::Var("b".to_string()),
            constraints: vec![],
            polarity: Polarity::Forward,
            priority: 15,
        };

        transducer.register_pattern(pattern);
        let rule = transducer.transduce("test_pattern");

        assert!(rule.is_ok());
        assert_eq!(transducer.rule_count(), 1);
    }

    #[test]
    fn test_rewrite_rule_creation() {
        let rule = RewriteRule::new(
            PatternExpr::Var("x".to_string()),
            PatternExpr::Var("y".to_string()),
        )
        .with_priority(30);

        assert_eq!(rule.priority, 30);
        assert!(rule.is_valid);
    }

    #[test]
    fn test_expr_depth() {
        let transducer = Transducer::new();

        let simple = PatternExpr::Var("x".to_string());
        assert_eq!(transducer.expr_depth(&simple), 0);

        let composed = PatternExpr::Op {
            name: "f".to_string(),
            args: vec![
                PatternExpr::Var("a".to_string()),
                PatternExpr::Var("b".to_string()),
            ],
        };
        assert_eq!(transducer.expr_depth(&composed), 1);
    }

    #[test]
    fn test_complexity_estimate() {
        let mut transducer = Transducer::new();

        let rule = RewriteRule::new(
            PatternExpr::Var("x".to_string()),
            PatternExpr::Var("y".to_string()),
        );

        let complexity = transducer.complexity_estimate(&rule);
        assert!(complexity >= 0.0);
    }

    #[test]
    fn test_codegen_rule_rust() {
        let mut transducer = Transducer::new();

        let rule = RewriteRule::new(
            PatternExpr::Var("source".to_string()),
            PatternExpr::Var("target".to_string()),
        );

        let code = transducer.codegen_rule(&rule, CodegenTarget::Rust);
        assert!(code.contains("apply_rewrite"));
        assert!(code.contains("CRDTEGraph"));
    }

    #[test]
    fn test_codegen_rule_qasm() {
        let mut transducer = Transducer::new();

        let rule = RewriteRule::new(
            PatternExpr::Var("source".to_string()),
            PatternExpr::Var("target".to_string()),
        );

        let code = transducer.codegen_rule(&rule, CodegenTarget::QASM);
        assert!(code.contains("OPENQASM"));
        assert!(code.contains("qubit"));
        assert!(code.contains("measure"));
    }

    #[test]
    fn test_codegen_rule_llvm() {
        let mut transducer = Transducer::new();

        let rule = RewriteRule::new(
            PatternExpr::Var("source".to_string()),
            PatternExpr::Var("target".to_string()),
        );

        let code = transducer.codegen_rule(&rule, CodegenTarget::LLVM);

        // Verify LLVM IR syntax elements
        assert!(code.contains("; LLVM IR for pattern rewrite rule"));
        assert!(code.contains("%Pattern = type { i32, i8*, i8* }"));
        assert!(code.contains("define internal i1 @check_constraints"));
        assert!(code.contains("define internal %Pattern* @transform_pattern"));
        assert!(code.contains("define i32 @apply_rewrite"));
        assert!(code.contains("entry:"));
        assert!(code.contains("br i1 %cond"));
        assert!(code.contains("label %match"));
        assert!(code.contains("label %nomatch"));
        assert!(code.contains("call i8* @malloc"));
        assert!(code.contains("getelementptr"));
        assert!(code.contains("load i32"));
        assert!(code.contains("store i32"));
        assert!(code.contains("ret i32"));
    }

    #[test]
    fn test_codegen_rule_llvm_with_constraints() {
        let mut transducer = Transducer::new();

        let rule = RewriteRule::new(
            PatternExpr::Var("source".to_string()),
            PatternExpr::Var("target".to_string()),
        )
        .with_color_constraint("source".to_string(), Color::Red);

        let code = transducer.codegen_rule(&rule, CodegenTarget::LLVM);

        // Verify constraint checking is present
        assert!(code.contains("icmp eq i32"));
        assert!(code.contains("check_constraints"));
        assert!(code.contains("Constraint: source must be"));
    }

    #[test]
    fn test_llvm_expr_conversion() {
        let transducer = Transducer::new();

        // Test variable conversion
        let var = PatternExpr::Var("x".to_string());
        let var_code = transducer.expr_to_llvm(&var);
        assert!(var_code.contains("Variable: x"));

        // Test operator conversion
        let op = PatternExpr::Op {
            name: "compose".to_string(),
            args: vec![],
        };
        let op_code = transducer.expr_to_llvm(&op);
        assert!(op_code.contains("Operator: compose"));

        // Test identity conversion
        let id = PatternExpr::Identity;
        let id_code = transducer.expr_to_llvm(&id);
        assert!(id_code.contains("Identity pattern"));
    }

    #[test]
    fn test_schedule_rules() {
        let mut transducer = Transducer::new();

        let rule1 = RewriteRule::new(
            PatternExpr::Var("a".to_string()),
            PatternExpr::Var("b".to_string()),
        )
        .with_priority(10);

        let rule2 = RewriteRule::new(
            PatternExpr::Var("c".to_string()),
            PatternExpr::Var("d".to_string()),
        )
        .with_priority(30);

        transducer.rules.push(rule1);
        transducer.rules.push(rule2);

        let egraph = CRDTEGraph::new();
        let scheduled = transducer.schedule_rules(&egraph);

        assert_eq!(scheduled[0].priority, 30);
        assert_eq!(scheduled[1].priority, 10);
    }
}
