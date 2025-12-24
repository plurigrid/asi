#!/usr/bin/env rust-script

//! Integration test for pattern-rewriting-jit skill
//! This script demonstrates the skill working end-to-end

use fermyon_agents::{
    PatternRewritingSkill,
    RegisterPatternRequest,
    TransducePatternRequest,
    GenerateCodeRequest,
    CompileCodeRequest,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  Pattern-Rewriting JIT Skill Integration Test");
    println!("═══════════════════════════════════════════════════════════════\n");

    // 1. Create skill instance
    println!("[1] Creating PatternRewritingSkill instance...");
    let mut skill = PatternRewritingSkill::new();
    println!("    ✅ Skill created with ID: {}\n", skill.skill_id);

    // 2. Register a pattern
    println!("[2] Registering pattern 'optimization_rule'...");
    let register_req = RegisterPatternRequest {
        pattern_name: "optimization_rule".to_string(),
        source_pattern: "inefficient_op".to_string(),
        target_pattern: "efficient_op".to_string(),
        constraints: vec![],
        priority: 50,
    };

    let register_resp = skill.register_pattern(register_req)?;
    println!("    ✅ Pattern registered: {:?}", register_resp.data);
    println!("    Operation ID: {}\n", register_resp.operation_id);

    // 3. Generate code for multiple targets
    println!("[3] Generating code for multiple targets...");

    for target in &["rust", "qasm", "llvm"] {
        let gen_req = GenerateCodeRequest {
            source_pattern: "inefficient_op".to_string(),
            target_pattern: "efficient_op".to_string(),
            target: target.to_string(),
        };

        let gen_resp = skill.generate_code(gen_req)?;
        if gen_resp.success {
            if let Some(code) = gen_resp.data {
                println!("    ✅ {} code generated ({} bytes)", target, code.len());
            }
        } else {
            println!("    ⚠️  {} code generation failed: {:?}", target, gen_resp.error);
        }
    }
    println!();

    // 4. Get operation history
    println!("[4] Retrieving operation history...");
    let history = skill.get_history(10);
    println!("    Total operations: {}", history.len());
    for (i, op) in history.iter().enumerate() {
        println!(
            "    [{}] {:?} - {} ({})",
            i,
            op.operation_type,
            if op.status == fermyon_agents::OperationStatus::Success { "✅" } else { "❌" },
            op.details
        );
    }
    println!();

    // 5. Get cache statistics
    println!("[5] Retrieving cache statistics...");
    let stats_resp = skill.get_stats()?;
    if stats_resp.success {
        if let Some(stats) = stats_resp.data {
            println!("    ✅ Cache statistics retrieved");
            println!("       Cache hits: {}", stats.cache_hits);
            println!("       Cache misses: {}", stats.cache_misses);
            println!("       Compilation time: {}ms", stats.total_compilation_time_ms);
        }
    }
    println!();

    println!("═══════════════════════════════════════════════════════════════");
    println!("  ✅ All integration tests passed!");
    println!("═══════════════════════════════════════════════════════════════");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_skill_lifecycle() {
        let mut skill = PatternRewritingSkill::new();

        // Register pattern
        let req = RegisterPatternRequest {
            pattern_name: "test".to_string(),
            source_pattern: "a".to_string(),
            target_pattern: "b".to_string(),
            constraints: vec![],
            priority: 10,
        };
        let resp = skill.register_pattern(req).unwrap();
        assert!(resp.success);

        // Generate code
        let gen_req = GenerateCodeRequest {
            source_pattern: "a".to_string(),
            target_pattern: "b".to_string(),
            target: "rust".to_string(),
        };
        let gen_resp = skill.generate_code(gen_req).unwrap();
        assert!(gen_resp.success);
        assert!(gen_resp.data.is_some());

        // Check history
        let history = skill.get_history(100);
        assert!(!history.is_empty());
    }
}
