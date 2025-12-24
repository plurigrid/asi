# Pattern-Rewriting JIT Compilation Skill - Installation Guide

## Overview

The **pattern-rewriting-jit** skill enables pattern-based code generation and JIT compilation for multi-target execution in Codex. It provides a clean API for registering patterns, transducing them to rewrite rules, generating code in multiple target languages (Rust, QASM, LLVM), and compiling LLVM IR to native code with automatic caching.

---

## Quick Start

### 1. Prerequisites

- **Rust** 1.90.0+ (or workaround for Spin SDK compatibility)
- **LLVM Tools** (for native code generation):
  ```bash
  # Ubuntu/Debian
  sudo apt-get install llvm clang binutils

  # macOS
  brew install llvm

  # Fedora/RHEL
  sudo dnf install llvm-tools clang binutils
  ```

### 2. Installation into Codex

#### Option A: Direct Installation (Development)

```bash
# Navigate to Codex installation directory
cd /path/to/codex

# Copy skill files
cp -r /Users/bob/ies/fermyon_agents fermyon_agents_skill

# Install dependencies
cd fermyon_agents_skill
cargo build --release

# Register skill with Codex
codex skill register \
  --manifest skill.manifest.json \
  --path ./target/release/libfermyon_agents.rlib
```

#### Option B: Using Codex Skill Manager

```bash
# If Codex has a skill manager (recommended)
codex skills install \
  --name pattern-rewriting-jit \
  --version 1.0.0 \
  --source /Users/bob/ies/fermyon_agents
```

#### Option C: Manual Registration (Advanced)

1. **Build the skill**:
   ```bash
   cd /Users/bob/ies/fermyon_agents
   cargo build --lib --release
   ```

2. **Create Codex integration file** (`codex_skill.json`):
   ```json
   {
     "skill_id": "pattern-rewriting-jit-v1.0.0",
     "module": "fermyon_agents",
     "main_type": "PatternRewritingSkill",
     "init_function": "new",
     "methods": [
       "register_pattern",
       "transduce_pattern",
       "generate_code",
       "compile_code",
       "get_stats"
     ],
     "config_defaults": {
       "optimization_level": 2,
       "cache_enabled": true,
       "max_cached_functions": 1000,
       "fallback_to_interpretation": true
     }
   }
   ```

3. **Register with Codex**:
   ```bash
   codex skills register \
     --config codex_skill.json \
     --library target/release/libfermyon_agents.rlib
   ```

---

## Configuration

### Default Configuration

The skill uses sensible defaults but can be customized:

```rust
PatternRewritingSkill::with_jit_config(JitConfig {
    work_dir: PathBuf::from("/tmp/pattern_jit"),
    cache_enabled: true,
    optimization_level: 2,        // -O2
    fallback_to_interpretation: true,
    max_cached_functions: 1000,
})
```

### Environment Variables (Optional)

```bash
export PATTERN_JIT_WORK_DIR=/var/cache/pattern_jit
export PATTERN_JIT_OPT_LEVEL=3
export PATTERN_JIT_CACHE_SIZE=5000
export PATTERN_JIT_FALLBACK=true
```

### Configuration via Codex

In Codex configuration file:

```yaml
skills:
  pattern-rewriting-jit:
    enabled: true
    config:
      optimization_level: 2
      cache_enabled: true
      max_cached_functions: 1000
      fallback_to_interpretation: true
      work_directory: /var/cache/pattern_jit
```

---

## Verification

### 1. Check Installation

```bash
# Verify skill is loaded in Codex
codex skills list | grep pattern-rewriting-jit

# Or directly
cargo test -p fermyon_agents
```

### 2. Run Built-in Tests

```bash
# Run all skill tests
cd /Users/bob/ies/fermyon_agents
cargo test skill_pattern_rewriting

# Run with output
cargo test skill_pattern_rewriting -- --nocapture
```

### 3. Integration Test

Create `test_skill_integration.rs`:

```rust
#[test]
fn test_skill_in_codex() {
    use fermyon_agents::PatternRewritingSkill;
    use fermyon_agents::RegisterPatternRequest;

    // Initialize skill
    let mut skill = PatternRewritingSkill::new();

    // Test pattern registration
    let register_req = RegisterPatternRequest {
        pattern_name: "test_pattern".to_string(),
        source_pattern: "x".to_string(),
        target_pattern: "y".to_string(),
        constraints: vec![],
        priority: 10,
    };

    let response = skill.register_pattern(register_req).unwrap();
    assert!(response.success);
    println!("✅ Skill registered successfully");

    // Test code generation
    use fermyon_agents::GenerateCodeRequest;

    let gen_req = GenerateCodeRequest {
        source_pattern: "source".to_string(),
        target_pattern: "target".to_string(),
        target: "rust".to_string(),
    };

    let response = skill.generate_code(gen_req).unwrap();
    assert!(response.success);
    assert!(response.data.is_some());
    println!("✅ Code generation works");

    // Test statistics
    let stats = skill.get_stats().unwrap();
    assert!(stats.success);
    println!("✅ Statistics retrieval works");
}
```

Run the integration test:

```bash
cargo test --test test_skill_integration -- --nocapture
```

---

## API Usage Examples

### Example 1: Using Skill Directly

```rust
use fermyon_agents::{
    PatternRewritingSkill,
    RegisterPatternRequest,
    GenerateCodeRequest,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create skill
    let mut skill = PatternRewritingSkill::new();

    // Register pattern
    let request = RegisterPatternRequest {
        pattern_name: "optimization_rule".to_string(),
        source_pattern: "inefficient_op".to_string(),
        target_pattern: "efficient_op".to_string(),
        constraints: vec![],
        priority: 50,
    };

    let response = skill.register_pattern(request)?;
    println!("Registered: {:?}", response);

    // Generate code
    let request = GenerateCodeRequest {
        source_pattern: "inefficient_op".to_string(),
        target_pattern: "efficient_op".to_string(),
        target: "llvm".to_string(),
    };

    let response = skill.generate_code(request)?;
    if response.success {
        println!("Generated LLVM IR:\n{}", response.data.unwrap());
    }

    Ok(())
}
```

### Example 2: In Codex Agent

```rust
// In your Codex agent
use fermyon_agents::PatternRewritingSkill;

pub struct MyAgent {
    skill: PatternRewritingSkill,
}

impl MyAgent {
    pub fn new() -> Self {
        Self {
            skill: PatternRewritingSkill::new(),
        }
    }

    pub fn optimize_pattern(&mut self, pattern_name: &str) -> Result<String, String> {
        use fermyon_agents::TransducePatternRequest;

        let request = TransducePatternRequest {
            pattern_name: pattern_name.to_string(),
        };

        match self.skill.transduce_pattern(request) {
            Ok(response) => {
                if response.success {
                    Ok(response.data.unwrap_or_default())
                } else {
                    Err(response.error.unwrap_or_else(|| "Unknown error".to_string()))
                }
            }
            Err(e) => Err(e),
        }
    }
}
```

### Example 3: HTTP Endpoint Integration

```rust
// Example Spin HTTP component using the skill

use spin_sdk::http::{IntoResponse, Request, Response};
use fermyon_agents::PatternRewritingSkill;

static SKILL: std::sync::Mutex<PatternRewritingSkill> =
    std::sync::Mutex::new(PatternRewritingSkill::new());

#[spin_sdk::http_component]
fn handle_pattern_request(req: Request) -> Response {
    match req.path() {
        "/skill/register" => {
            let skill = SKILL.lock().unwrap();
            // Handle POST request to register pattern
            Response::builder()
                .status(200)
                .body("Pattern registered")
                .build()
        }
        "/skill/compile" => {
            let skill = SKILL.lock().unwrap();
            // Handle POST request to compile
            Response::builder()
                .status(200)
                .body("Compilation started")
                .build()
        }
        _ => Response::builder()
            .status(404)
            .body("Not found")
            .build(),
    }
}
```

---

## Troubleshooting

### Issue: "LLVM tools not found"

**Symptom**: Compilation fails with "Is LLVM installed?"

**Solution**:
```bash
# Install LLVM tools
sudo apt-get install llvm clang  # Debian/Ubuntu
brew install llvm                # macOS
sudo dnf install llvm-tools      # Fedora

# Verify installation
llvm-as --version
opt --version
llc --version
```

### Issue: "Skill not found in Codex"

**Symptom**: `codex skills list` doesn't show pattern-rewriting-jit

**Solution**:
```bash
# Rebuild the library
cd /Users/bob/ies/fermyon_agents
cargo clean
cargo build --lib --release

# Re-register with Codex
codex skills register \
  --manifest skill.manifest.json \
  --library target/release/libfermyon_agents.rlib
```

### Issue: Tests failing

**Symptom**: `cargo test` fails with compilation errors

**Workaround** (for Spin SDK compatibility):
```bash
# Use Rust 1.90.0
rustup default 1.90.0

# Then run tests
cargo test skill_pattern_rewriting
```

### Issue: Cache permission denied

**Symptom**: Compilation fails with permission error on `/tmp/pattern_jit`

**Solution**:
```bash
# Create cache directory with proper permissions
sudo mkdir -p /var/cache/pattern_jit
sudo chmod 755 /var/cache/pattern_jit

# Or use custom work directory
export PATTERN_JIT_WORK_DIR=$HOME/.pattern_jit
```

---

## Deployment

### For Production Use

1. **Build optimized binary**:
   ```bash
   cargo build --release --lib
   ```

2. **Run tests before deployment**:
   ```bash
   cargo test --release
   ```

3. **Deploy to Codex**:
   ```bash
   codex deploy skill \
     --name pattern-rewriting-jit \
     --version 1.0.0 \
     --library target/release/libfermyon_agents.rlib
   ```

### For WASM/Serverless

The skill works in WASM environments with graceful degradation:

```rust
let config = JitConfig {
    fallback_to_interpretation: true,  // Important for WASM
    ..Default::default()
};
let skill = PatternRewritingSkill::with_jit_config(config);
```

When LLVM tools aren't available (common in serverless), the skill will:
1. Attempt compilation
2. Gracefully fall back to interpretation
3. Return appropriate error messages

---

## API Reference

### Skill Methods

| Method | Input | Output | Description |
|--------|-------|--------|-------------|
| `new()` | - | `PatternRewritingSkill` | Create skill |
| `register_pattern()` | `RegisterPatternRequest` | `SkillResponse<String>` | Register pattern |
| `transduce_pattern()` | `TransducePatternRequest` | `SkillResponse<String>` | Transduce to rule |
| `generate_code()` | `GenerateCodeRequest` | `SkillResponse<String>` | Generate code |
| `compile_code()` | `CompileCodeRequest` | `SkillResponse<CompilationResult>` | Compile LLVM |
| `get_stats()` | - | `SkillResponse<CacheStatistics>` | Get statistics |
| `get_history()` | `limit: usize` | `Vec<SkillOperation>` | Get operation history |

### Request Types

```rust
// Register pattern
struct RegisterPatternRequest {
    pattern_name: String,
    source_pattern: String,
    target_pattern: String,
    constraints: Vec<String>,
    priority: u32,
}

// Generate code
struct GenerateCodeRequest {
    source_pattern: String,
    target_pattern: String,
    target: String,  // "rust", "qasm", or "llvm"
}

// Compile code
struct CompileCodeRequest {
    llvm_ir: String,
    pattern_id: String,
}
```

---

## Support

For issues or questions:

1. Check the [Troubleshooting](#troubleshooting) section
2. Review the inline documentation:
   - `src/skill_pattern_rewriting.rs` - Skill implementation
   - `JIT_INTEGRATION.md` - JIT compilation details
   - `LLVM_INTEGRATION.md` - LLVM code generation
3. Run tests with `cargo test -- --nocapture`
4. Check operation history: `skill.get_history(50)`

---

## License

MIT - See LICENSE file

---

**Status**: ✅ Ready for Codex Installation
**Version**: 1.0.0
**Last Updated**: 2025-12-21
