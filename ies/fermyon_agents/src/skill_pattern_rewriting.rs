/*!
    Skill: Pattern-Rewriting JIT Compilation

    High-level API for pattern-based code generation and JIT compilation.
    Provides clean interfaces for Codex integration and agent skill registration.
*/

use crate::{
    Transducer, RewriteRule, TopologicalPattern, PatternExpr, CodegenTarget,
    JitCompiler, JitConfig, CompiledFunction, CacheStatistics,
    RewritePolarity,
};
use std::collections::HashMap;
use std::path::PathBuf;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Skill context for pattern rewriting operations
#[derive(Debug, Clone)]
pub struct PatternRewritingSkill {
    pub skill_id: String,
    pub transducer: Transducer,
    pub jit_compiler: JitCompiler,
    pub operation_history: Vec<SkillOperation>,
}

/// Record of a skill operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SkillOperation {
    pub operation_id: String,
    pub operation_type: OperationType,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub status: OperationStatus,
    pub details: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum OperationType {
    RegisterPattern,
    TransducePattern,
    GenerateCode,
    CompileCode,
    CacheHit,
    CacheMiss,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum OperationStatus {
    Success,
    Failure,
    Pending,
}

/// API Request for pattern registration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegisterPatternRequest {
    pub pattern_name: String,
    pub source_pattern: String,
    pub target_pattern: String,
    pub constraints: Vec<String>,
    pub priority: u32,
}

/// API Request for pattern transduction
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransducePatternRequest {
    pub pattern_name: String,
}

/// API Request for code generation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GenerateCodeRequest {
    pub source_pattern: String,
    pub target_pattern: String,
    pub target: String, // "rust", "qasm", "llvm"
}

/// API Request for JIT compilation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompileCodeRequest {
    pub llvm_ir: String,
    pub pattern_id: String,
}

/// API Response for successful operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SkillResponse<T> {
    pub success: bool,
    pub operation_id: String,
    pub data: Option<T>,
    pub error: Option<String>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

impl PatternRewritingSkill {
    /// Create new skill instance
    pub fn new() -> Self {
        Self {
            skill_id: Uuid::new_v4().to_string(),
            transducer: Transducer::new(),
            jit_compiler: JitCompiler::new(JitConfig::default()),
            operation_history: Vec::new(),
        }
    }

    /// Create skill with custom JIT configuration
    pub fn with_jit_config(jit_config: JitConfig) -> Self {
        Self {
            skill_id: Uuid::new_v4().to_string(),
            transducer: Transducer::new(),
            jit_compiler: JitCompiler::new(jit_config),
            operation_history: Vec::new(),
        }
    }

    /// Register a pattern (API endpoint handler)
    pub fn register_pattern(
        &mut self,
        request: RegisterPatternRequest,
    ) -> Result<SkillResponse<String>, String> {
        let op_id = Uuid::new_v4().to_string();

        // Parse pattern expressions (simplified parsing)
        let source = PatternExpr::Var(request.source_pattern.clone());
        let target = PatternExpr::Var(request.target_pattern.clone());

        // Create topological pattern
        let pattern = TopologicalPattern {
            name: request.pattern_name.clone(),
            source_pattern: source,
            target_pattern: target,
            constraints: vec![], // Constraints would be parsed from request
            polarity: RewritePolarity::Forward,
            priority: request.priority,
        };

        // Register pattern
        self.transducer.register_pattern(pattern);

        // Record operation
        self.record_operation(
            &op_id,
            OperationType::RegisterPattern,
            OperationStatus::Success,
            format!("Registered pattern: {}", request.pattern_name),
        );

        Ok(SkillResponse {
            success: true,
            operation_id: op_id,
            data: Some(request.pattern_name),
            error: None,
            timestamp: chrono::Utc::now(),
        })
    }

    /// Transduce pattern to rewrite rule (API endpoint handler)
    pub fn transduce_pattern(
        &mut self,
        request: TransducePatternRequest,
    ) -> Result<SkillResponse<String>, String> {
        let op_id = Uuid::new_v4().to_string();

        match self.transducer.transduce(&request.pattern_name) {
            Ok(rule) => {
                self.record_operation(
                    &op_id,
                    OperationType::TransducePattern,
                    OperationStatus::Success,
                    format!("Transduced pattern: {}", request.pattern_name),
                );

                Ok(SkillResponse {
                    success: true,
                    operation_id: op_id,
                    data: Some(format!("Rule generated for {}", request.pattern_name)),
                    error: None,
                    timestamp: chrono::Utc::now(),
                })
            }
            Err(e) => {
                self.record_operation(
                    &op_id,
                    OperationType::TransducePattern,
                    OperationStatus::Failure,
                    format!("Failed to transduce: {}", e),
                );

                Ok(SkillResponse {
                    success: false,
                    operation_id: op_id,
                    data: None,
                    error: Some(e),
                    timestamp: chrono::Utc::now(),
                })
            }
        }
    }

    /// Generate code for rewrite rule (API endpoint handler)
    pub fn generate_code(
        &mut self,
        request: GenerateCodeRequest,
    ) -> Result<SkillResponse<String>, String> {
        let op_id = Uuid::new_v4().to_string();

        // Create rule from expressions
        let rule = RewriteRule::new(
            PatternExpr::Var(request.source_pattern.clone()),
            PatternExpr::Var(request.target_pattern.clone()),
        );

        // Parse target
        let target = match request.target.as_str() {
            "rust" => CodegenTarget::Rust,
            "qasm" => CodegenTarget::QASM,
            "llvm" => CodegenTarget::LLVM,
            _ => CodegenTarget::Rust,
        };

        // Generate code
        let code = self.transducer.codegen_rule(&rule, target);

        self.record_operation(
            &op_id,
            OperationType::GenerateCode,
            OperationStatus::Success,
            format!("Generated {} code ({} bytes)", request.target, code.len()),
        );

        Ok(SkillResponse {
            success: true,
            operation_id: op_id,
            data: Some(code),
            error: None,
            timestamp: chrono::Utc::now(),
        })
    }

    /// Compile LLVM IR to native code (API endpoint handler)
    pub fn compile_code(
        &mut self,
        request: CompileCodeRequest,
    ) -> Result<SkillResponse<CompilationResult>, String> {
        let op_id = Uuid::new_v4().to_string();

        match self.jit_compiler.compile_llvm_ir(&request.llvm_ir, &request.pattern_id) {
            Ok(compiled) => {
                let path_str = compiled
                    .native_code_path
                    .as_ref()
                    .map(|p| p.to_string_lossy().to_string())
                    .unwrap_or_else(|| "unknown".to_string());

                self.record_operation(
                    &op_id,
                    OperationType::CompileCode,
                    OperationStatus::Success,
                    format!("Compiled to {} in {} ms", path_str, compiled.compilation_time_ms),
                );

                Ok(SkillResponse {
                    success: true,
                    operation_id: op_id,
                    data: Some(CompilationResult {
                        pattern_id: compiled.pattern_id,
                        native_code_path: path_str,
                        compilation_time_ms: compiled.compilation_time_ms,
                        success: true,
                    }),
                    error: None,
                    timestamp: chrono::Utc::now(),
                })
            }
            Err(e) => {
                self.record_operation(
                    &op_id,
                    OperationType::CompileCode,
                    OperationStatus::Failure,
                    format!("Compilation failed: {}", e),
                );

                Ok(SkillResponse {
                    success: false,
                    operation_id: op_id,
                    data: None,
                    error: Some(e),
                    timestamp: chrono::Utc::now(),
                })
            }
        }
    }

    /// Get compilation statistics (API endpoint handler)
    pub fn get_stats(&self) -> Result<SkillResponse<CacheStatistics>, String> {
        let op_id = Uuid::new_v4().to_string();

        match self.jit_compiler.get_cache_stats() {
            Ok(stats) => Ok(SkillResponse {
                success: true,
                operation_id: op_id,
                data: Some(stats),
                error: None,
                timestamp: chrono::Utc::now(),
            }),
            Err(e) => Ok(SkillResponse {
                success: false,
                operation_id: op_id,
                data: None,
                error: Some(e),
                timestamp: chrono::Utc::now(),
            }),
        }
    }

    /// Get operation history
    pub fn get_history(&self, limit: usize) -> Vec<SkillOperation> {
        self.operation_history
            .iter()
            .rev()
            .take(limit)
            .cloned()
            .collect()
    }

    /// Clear operation history
    pub fn clear_history(&mut self) {
        self.operation_history.clear();
    }

    // Private helpers

    fn record_operation(
        &mut self,
        op_id: &str,
        op_type: OperationType,
        status: OperationStatus,
        details: String,
    ) {
        self.operation_history.push(SkillOperation {
            operation_id: op_id.to_string(),
            operation_type: op_type,
            timestamp: chrono::Utc::now(),
            status,
            details,
        });
    }
}

/// Result of compilation operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilationResult {
    pub pattern_id: String,
    pub native_code_path: String,
    pub compilation_time_ms: u64,
    pub success: bool,
}

impl Default for PatternRewritingSkill {
    fn default() -> Self {
        Self::new()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_skill_creation() {
        let skill = PatternRewritingSkill::new();
        assert!(!skill.skill_id.is_empty());
        assert!(skill.operation_history.is_empty());
    }

    #[test]
    fn test_skill_with_custom_config() {
        let config = JitConfig {
            optimization_level: 3,
            ..Default::default()
        };
        let skill = PatternRewritingSkill::with_jit_config(config);
        assert_eq!(skill.jit_compiler.config.optimization_level, 3);
    }

    #[test]
    fn test_register_pattern() {
        let mut skill = PatternRewritingSkill::new();

        let request = RegisterPatternRequest {
            pattern_name: "test_pattern".to_string(),
            source_pattern: "x".to_string(),
            target_pattern: "y".to_string(),
            constraints: vec![],
            priority: 10,
        };

        let response = skill.register_pattern(request).unwrap();
        assert!(response.success);
        assert!(response.data.is_some());
        assert_eq!(skill.operation_history.len(), 1);
    }

    #[test]
    fn test_operation_recording() {
        let mut skill = PatternRewritingSkill::new();

        let request = RegisterPatternRequest {
            pattern_name: "test".to_string(),
            source_pattern: "a".to_string(),
            target_pattern: "b".to_string(),
            constraints: vec![],
            priority: 20,
        };

        let _ = skill.register_pattern(request);

        let history = skill.get_history(10);
        assert_eq!(history.len(), 1);
        assert_eq!(history[0].operation_type, OperationType::RegisterPattern);
        assert_eq!(history[0].status, OperationStatus::Success);
    }

    #[test]
    fn test_clear_history() {
        let mut skill = PatternRewritingSkill::new();

        let request = RegisterPatternRequest {
            pattern_name: "test".to_string(),
            source_pattern: "x".to_string(),
            target_pattern: "y".to_string(),
            constraints: vec![],
            priority: 15,
        };

        let _ = skill.register_pattern(request);
        assert!(!skill.operation_history.is_empty());

        skill.clear_history();
        assert!(skill.operation_history.is_empty());
    }

    #[test]
    fn test_generate_code_request() {
        let mut skill = PatternRewritingSkill::new();

        let request = GenerateCodeRequest {
            source_pattern: "source".to_string(),
            target_pattern: "target".to_string(),
            target: "rust".to_string(),
        };

        let response = skill.generate_code(request).unwrap();
        assert!(response.success);
        assert!(response.data.is_some());
    }

    #[test]
    fn test_get_stats() {
        let skill = PatternRewritingSkill::new();
        let response = skill.get_stats().unwrap();
        assert!(response.success);
        assert!(response.data.is_some());
    }

    #[test]
    fn test_skill_response_serialization() {
        let response: SkillResponse<String> = SkillResponse {
            success: true,
            operation_id: "test_op".to_string(),
            data: Some("test_data".to_string()),
            error: None,
            timestamp: chrono::Utc::now(),
        };

        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("test_op"));
        assert!(json.contains("test_data"));
    }
}
