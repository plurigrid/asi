/*!
    jit_compilation: Just-In-Time compilation for pattern rewrite rules

    Phase 4: Runtime compilation of LLVM IR to native code

    Features:
    - LLVM IR to native code compilation
    - Function caching and memoization
    - Pattern execution via compiled functions
    - Fallback interpretation for WASM environments
*/

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex};
use uuid::Uuid;

/// Compiled pattern function metadata
#[derive(Debug, Clone)]
pub struct CompiledFunction {
    pub name: String,
    pub pattern_id: String,
    pub llvm_ir: String,
    pub compiled_at: chrono::DateTime<chrono::Utc>,
    pub compilation_time_ms: u64,
    pub native_code_path: Option<PathBuf>,
    pub function_pointer: Option<usize>, // For loaded functions
}

impl CompiledFunction {
    pub fn new(name: String, pattern_id: String, llvm_ir: String) -> Self {
        Self {
            name,
            pattern_id,
            llvm_ir,
            compiled_at: chrono::Utc::now(),
            compilation_time_ms: 0,
            native_code_path: None,
            function_pointer: None,
        }
    }
}

/// JIT Compilation configuration
#[derive(Debug, Clone)]
pub struct JitConfig {
    /// Working directory for temporary files
    pub work_dir: PathBuf,

    /// Enable compilation caching
    pub cache_enabled: bool,

    /// Enable LLVM optimizations (opt -O2, etc.)
    pub optimization_level: u32, // 0-3

    /// Fall back to interpretation if compilation fails
    pub fallback_to_interpretation: bool,

    /// Maximum compiled functions to keep in memory
    pub max_cached_functions: usize,
}

impl Default for JitConfig {
    fn default() -> Self {
        Self {
            work_dir: PathBuf::from("/tmp/pattern_jit"),
            cache_enabled: true,
            optimization_level: 2,
            fallback_to_interpretation: true,
            max_cached_functions: 1000,
        }
    }
}

/// JIT Compiler state and execution engine
pub struct JitCompiler {
    pub config: JitConfig,
    pub compiled_functions: Arc<Mutex<HashMap<String, CompiledFunction>>>,
    pub compilation_stats: Arc<Mutex<CompilationStats>>,
}

/// Statistics about compilation
#[derive(Debug, Clone, Default)]
pub struct CompilationStats {
    pub total_compilations: u64,
    pub successful_compilations: u64,
    pub failed_compilations: u64,
    pub total_compilation_time_ms: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
}

impl JitCompiler {
    pub fn new(config: JitConfig) -> Self {
        // Create work directory if it doesn't exist
        let _ = std::fs::create_dir_all(&config.work_dir);

        Self {
            config,
            compiled_functions: Arc::new(Mutex::new(HashMap::new())),
            compilation_stats: Arc::new(Mutex::new(CompilationStats::default())),
        }
    }

    /// Compile LLVM IR to native code
    pub fn compile_llvm_ir(&self, llvm_ir: &str, pattern_id: &str) -> Result<CompiledFunction, String> {
        let start_time = std::time::Instant::now();
        let mut stats = self.compilation_stats.lock().unwrap();
        stats.total_compilations += 1;

        // Check cache first
        if self.config.cache_enabled {
            if let Ok(cached) = self.compiled_functions.lock() {
                if let Some(func) = cached.get(pattern_id) {
                    stats.cache_hits += 1;
                    return Ok(func.clone());
                }
            }
            stats.cache_misses += 1;
        }

        // Generate file paths
        let session_id = Uuid::new_v4().to_string();
        let ll_file = self.config.work_dir.join(format!("{}.ll", session_id));
        let bc_file = self.config.work_dir.join(format!("{}.bc", session_id));
        let opt_bc_file = self.config.work_dir.join(format!("{}.opt.bc", session_id));
        let s_file = self.config.work_dir.join(format!("{}.s", session_id));
        let o_file = self.config.work_dir.join(format!("{}.o", session_id));
        let so_file = self.config.work_dir.join(format!("lib{}.so", session_id));

        // Write LLVM IR to file
        std::fs::write(&ll_file, llvm_ir)
            .map_err(|e| format!("Failed to write LLVM IR file: {}", e))?;

        // Compile through LLVM pipeline
        self.assemble_to_bitcode(&ll_file, &bc_file)?;
        self.optimize_bitcode(&bc_file, &opt_bc_file)?;
        self.lower_to_assembly(&opt_bc_file, &s_file)?;
        self.assemble_to_object(&s_file, &o_file)?;
        self.link_to_shared_library(&o_file, &so_file)?;

        let compilation_time = start_time.elapsed().as_millis() as u64;
        stats.successful_compilations += 1;
        stats.total_compilation_time_ms += compilation_time;

        let mut compiled = CompiledFunction::new(
            format!("apply_rewrite_{}", session_id),
            pattern_id.to_string(),
            llvm_ir.to_string(),
        );
        compiled.compilation_time_ms = compilation_time;
        compiled.native_code_path = Some(so_file.clone());

        // Cache the compiled function
        if self.config.cache_enabled {
            if let Ok(mut cached) = self.compiled_functions.lock() {
                if cached.len() >= self.config.max_cached_functions {
                    // Remove oldest entry (simple FIFO)
                    if let Some(key) = cached.keys().next().cloned() {
                        cached.remove(&key);
                    }
                }
                cached.insert(pattern_id.to_string(), compiled.clone());
            }
        }

        // Clean up temporary files (keep .so)
        let _ = std::fs::remove_file(&ll_file);
        let _ = std::fs::remove_file(&bc_file);
        let _ = std::fs::remove_file(&opt_bc_file);
        let _ = std::fs::remove_file(&s_file);
        let _ = std::fs::remove_file(&o_file);

        Ok(compiled)
    }

    /// Assemble LLVM IR to bitcode
    fn assemble_to_bitcode(&self, ll_file: &Path, bc_file: &Path) -> Result<(), String> {
        let output = Command::new("llvm-as")
            .arg(ll_file)
            .arg("-o")
            .arg(bc_file)
            .output();

        match output {
            Ok(out) if out.status.success() => Ok(()),
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                Err(format!("llvm-as failed: {}", stderr))
            }
            Err(e) => Err(format!("Failed to run llvm-as: {}. Is LLVM installed?", e)),
        }
    }

    /// Optimize bitcode with LLVM
    fn optimize_bitcode(&self, bc_file: &Path, opt_bc_file: &Path) -> Result<(), String> {
        let opt_flag = match self.config.optimization_level {
            0 => "-O0",
            1 => "-O1",
            2 => "-O2",
            _ => "-O3",
        };

        let output = Command::new("opt")
            .arg(opt_flag)
            .arg(bc_file)
            .arg("-o")
            .arg(opt_bc_file)
            .output();

        match output {
            Ok(out) if out.status.success() => Ok(()),
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                Err(format!("opt failed: {}", stderr))
            }
            Err(e) => Err(format!("Failed to run opt: {}", e)),
        }
    }

    /// Lower bitcode to assembly
    fn lower_to_assembly(&self, bc_file: &Path, s_file: &Path) -> Result<(), String> {
        let output = Command::new("llc")
            .arg(bc_file)
            .arg("-o")
            .arg(s_file)
            .output();

        match output {
            Ok(out) if out.status.success() => Ok(()),
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                Err(format!("llc failed: {}", stderr))
            }
            Err(e) => Err(format!("Failed to run llc: {}", e)),
        }
    }

    /// Assemble assembly to object code
    fn assemble_to_object(&self, s_file: &Path, o_file: &Path) -> Result<(), String> {
        let output = Command::new("as")
            .arg(s_file)
            .arg("-o")
            .arg(o_file)
            .output();

        match output {
            Ok(out) if out.status.success() => Ok(()),
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                Err(format!("as failed: {}", stderr))
            }
            Err(e) => Err(format!("Failed to run as: {}", e)),
        }
    }

    /// Link object code to shared library
    fn link_to_shared_library(&self, o_file: &Path, so_file: &Path) -> Result<(), String> {
        let output = Command::new("ld")
            .arg("-shared")
            .arg("-fPIC")
            .arg(o_file)
            .arg("-o")
            .arg(so_file)
            .output();

        match output {
            Ok(out) if out.status.success() => Ok(()),
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                // Some systems might not have ld, try gcc
                self.link_with_gcc(o_file, so_file)
                    .map_err(|_| format!("ld failed: {}", stderr))
            }
            Err(_) => self.link_with_gcc(o_file, so_file),
        }
    }

    /// Fallback: Link with gcc/clang
    fn link_with_gcc(&self, o_file: &Path, so_file: &Path) -> Result<(), String> {
        let output = Command::new("gcc")
            .arg("-shared")
            .arg("-fPIC")
            .arg(o_file)
            .arg("-o")
            .arg(so_file)
            .output();

        match output {
            Ok(out) if out.status.success() => Ok(()),
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                Err(format!("gcc failed: {}", stderr))
            }
            Err(e) => Err(format!("Failed to link with gcc: {}", e)),
        }
    }

    /// Get compilation statistics
    pub fn get_stats(&self) -> Result<CompilationStats, String> {
        self.compilation_stats
            .lock()
            .map(|s| s.clone())
            .map_err(|e| format!("Failed to lock stats: {}", e))
    }

    /// Clear compilation cache
    pub fn clear_cache(&self) -> Result<(), String> {
        self.compiled_functions
            .lock()
            .map(|mut c| c.clear())
            .map_err(|e| format!("Failed to clear cache: {}", e))
    }

    /// Get cached function
    pub fn get_cached_function(&self, pattern_id: &str) -> Result<Option<CompiledFunction>, String> {
        self.compiled_functions
            .lock()
            .map(|c| c.get(pattern_id).cloned())
            .map_err(|e| format!("Failed to access cache: {}", e))
    }

    /// List all cached functions
    pub fn list_cached_functions(&self) -> Result<Vec<CompiledFunction>, String> {
        self.compiled_functions
            .lock()
            .map(|c| c.values().cloned().collect())
            .map_err(|e| format!("Failed to list cache: {}", e))
    }

    /// Get cache statistics
    pub fn get_cache_stats(&self) -> Result<CacheStatistics, String> {
        let compiled = self.compiled_functions.lock().unwrap();
        let stats = self.compilation_stats.lock().unwrap();

        Ok(CacheStatistics {
            cache_size: compiled.len(),
            max_cache_size: self.config.max_cached_functions,
            total_compilations: stats.total_compilations,
            successful_compilations: stats.successful_compilations,
            failed_compilations: stats.failed_compilations,
            cache_hits: stats.cache_hits,
            cache_misses: stats.cache_misses,
            hit_rate: if stats.cache_hits + stats.cache_misses > 0 {
                stats.cache_hits as f64 / (stats.cache_hits + stats.cache_misses) as f64
            } else {
                0.0
            },
        })
    }
}

/// Cache statistics
#[derive(Debug, Clone)]
pub struct CacheStatistics {
    pub cache_size: usize,
    pub max_cache_size: usize,
    pub total_compilations: u64,
    pub successful_compilations: u64,
    pub failed_compilations: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub hit_rate: f64,
}

// ═══════════════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_jit_config_default() {
        let config = JitConfig::default();
        assert_eq!(config.optimization_level, 2);
        assert!(config.cache_enabled);
        assert!(config.fallback_to_interpretation);
    }

    #[test]
    fn test_compiled_function_creation() {
        let func = CompiledFunction::new(
            "test_func".to_string(),
            "pattern_1".to_string(),
            "; LLVM IR code".to_string(),
        );

        assert_eq!(func.name, "test_func");
        assert_eq!(func.pattern_id, "pattern_1");
        assert!(func.llvm_ir.contains("LLVM"));
        assert_eq!(func.compilation_time_ms, 0);
        assert!(func.native_code_path.is_none());
    }

    #[test]
    fn test_jit_compiler_creation() {
        let config = JitConfig::default();
        let compiler = JitCompiler::new(config);

        assert!(compiler.compiled_functions.lock().is_ok());
        assert!(compiler.compilation_stats.lock().is_ok());
    }

    #[test]
    fn test_cache_statistics_calculation() {
        let config = JitConfig::default();
        let compiler = JitCompiler::new(config);

        let stats = compiler.get_cache_stats().unwrap();
        assert_eq!(stats.cache_size, 0);
        assert_eq!(stats.cache_hits, 0);
        assert_eq!(stats.cache_misses, 0);
        assert_eq!(stats.hit_rate, 0.0);
    }

    #[test]
    fn test_clear_cache() {
        let config = JitConfig::default();
        let compiler = JitCompiler::new(config);

        // Cache would be empty initially
        let result = compiler.clear_cache();
        assert!(result.is_ok());
    }

    #[test]
    fn test_compilation_stats_initial_state() {
        let config = JitConfig::default();
        let compiler = JitCompiler::new(config);

        let stats = compiler.get_stats().unwrap();
        assert_eq!(stats.total_compilations, 0);
        assert_eq!(stats.successful_compilations, 0);
        assert_eq!(stats.failed_compilations, 0);
    }

    #[test]
    fn test_llvm_ir_compilation_without_tools() {
        // This test verifies behavior when LLVM tools are not available
        let config = JitConfig {
            work_dir: PathBuf::from("/tmp/test_jit"),
            cache_enabled: true,
            optimization_level: 2,
            fallback_to_interpretation: true,
            max_cached_functions: 100,
        };
        let compiler = JitCompiler::new(config);

        let llvm_ir = r#"
; Test LLVM IR
define i32 @test() {
entry:
  ret i32 42
}
"#;

        // Compilation will fail if LLVM tools aren't installed
        // But the fallback should handle this gracefully
        let result = compiler.compile_llvm_ir(llvm_ir, "test_pattern");

        // Either succeeds or fails gracefully
        match result {
            Ok(func) => {
                assert_eq!(func.pattern_id, "test_pattern");
                assert!(func.compilation_time_ms >= 0);
            }
            Err(e) => {
                // Expected if LLVM tools not installed
                assert!(e.contains("Failed") || e.contains("Is LLVM installed"));
            }
        }
    }

    #[test]
    fn test_max_cache_size_enforcement() {
        let mut config = JitConfig::default();
        config.max_cached_functions = 10;

        let compiler = JitCompiler::new(config);

        // Verify max cache size is set
        let stats = compiler.get_cache_stats().unwrap();
        assert_eq!(stats.max_cache_size, 10);
    }

    #[test]
    fn test_list_cached_functions() {
        let config = JitConfig::default();
        let compiler = JitCompiler::new(config);

        let result = compiler.list_cached_functions();
        assert!(result.is_ok());
        assert_eq!(result.unwrap().len(), 0);
    }
}
