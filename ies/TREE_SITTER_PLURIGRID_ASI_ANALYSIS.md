# Tree-Sitter Integration Analysis for Plurigrid/ASI

**Date**: December 22, 2025
**Purpose**: Determine optimal tree-sitter skill integration for spectral architecture + plurigrid/asi
**Status**: Analysis & Design Complete

---

## Executive Summary

The plurigrid/asi system is a **multi-language, multi-prover verification framework** requiring sophisticated code analysis across 6+ theorem provers. Tree-sitter can provide:

1. **Unified AST Analysis** - Parse code across Julia, Rust, Python, Lean4, Coq, etc.
2. **Multi-Prover Symbol Resolution** - Track theorems and proofs across language boundaries
3. **Dependency Graph Construction** - Build proof dependency networks for spectral architecture
4. **Cross-Language Comprehension** - Enable intelligent theorem discovery

---

## Current Architecture

### Plurigrid/ASI System Structure

```
plurigrid/asi (Master Verification System)
│
├── Theorem Provers (6 languages)
│   ├── Dafny            (.dfy files, 1,822 lines)
│   ├── Stellogen        (.sg files, 21 test files)
│   ├── Lean4            (.lean files, 2,448+ lines, 14 modules)
│   ├── Coq              (.v files, 3 files)
│   ├── Agda             (.agda files, 48+ files)
│   └── Idris            (.idr files, 63+ files)
│
├── Proof Catalog (5,652+ theorems)
│   ├── Global Index (proof-cache/)
│   ├── Cross-Prover Mappings
│   └── Equivalence Proofs
│
├── Orchestration (Julia + Rust)
│   ├── unified-verification.jl      (Master coordinator)
│   ├── agent-orchestrator (Rust)    (Parallel execution)
│   ├── interaction-timeline (Rust)  (State tracking)
│   └── Dashboard (Rust)             (UI/Monitoring)
│
└── Integration with Spectral Architecture
    ├── Music-Topos/.codex/skills/ (6 spectral modules)
    ├── Agents/ (Phase 2 Stages 1-2)
    └── Hatchery Repos (25+ plurigrid projects)
```

### Music-Topos/Agents (Our Current Work)

```
music-topos/agents/
│
├── Phase 2 Stage 1: Health Monitoring (750 lines)
│   ├── spectral_skills.jl           (150+ lines)
│   ├── health_tracking.jl           (200+ lines)
│   └── test_health_monitoring.jl    (400+ lines, 9/9 PASS)
│
├── Phase 2 Stage 2: Comprehension Discovery (800 lines)
│   ├── comprehension_discovery.jl   (400+ lines)
│   └── test_comprehension_discovery.jl (400+ lines, 9/9 PASS)
│
├── Phase 1: Spectral Skills (2,650 lines, 6 modules deployed)
│   ├── spectral_analyzer.jl
│   ├── mobius_filter.jl
│   ├── bidirectional_index.jl
│   ├── safe_rewriting.jl
│   ├── spectral_random_walk.jl
│   └── continuous_inversion.jl
│
└── Supporting Infrastructure
    └── .codex/skills/ (33 total skills)
```

### Language Distribution in Music-Topos

```
TypeScript:      1,832 files  (JS/TS infrastructure)
Markdown:          419 files  (Documentation)
JSON:              250 files  (Config, data)
Ruby:              136 files  (Testing, scripting)
HTML:              179 files  (Web frontend)
Python:             49 files  (Utilities, analysis)
Clojure:            84 files  (REPL, testing)
Julia:              30 files  (Core algorithms)
Rust:               24 files  (Performance modules)
Bash:                5 files  (Scripts)
SQL:                13 files  (Queries, schemas)
CSS:                 5 files  (Styling)
```

---

## How We Currently Use Code Analysis

### Phase 1: Spectral Architecture

1. **Manual Code Analysis**
   - Read Julia files to understand module structure
   - Track function signatures and exports
   - Verify imports and dependencies
   - Check type annotations

2. **Pattern Matching**
   - Find functions by name grep (e.g., `gap_to_emoji`)
   - Locate struct definitions
   - Trace function calls manually
   - Verify error handling

3. **Testing & Validation**
   - Run test scripts
   - Check test coverage manually
   - Verify output correctness
   - Benchmark performance

### Phase 2: Agent Integration

1. **Module Integration**
   - Include modules in agents
   - Track dependencies (spectral_skills → spectral_random_walk)
   - Verify circular dependency absence
   - Manage state sharing

2. **Cross-Module Communication**
   - Health monitoring (Stage 1) → Comprehension discovery (Stage 2)
   - Shared data structures (SystemHealthStatus)
   - Thread-safe access patterns
   - Integration testing

3. **Documentation & Discovery**
   - Manual module documentation
   - Function signature cataloging
   - Usage example creation
   - Integration guide writing

---

## Tree-Sitter Capabilities That Would Help

### Analysis We Could Automate

**1. Module Dependency Analysis**
```julia
# Current: Manual tracking
# Tree-Sitter: Automatic detection
- Find all `import` statements
- Extract module names being imported
- Build dependency graph
- Detect circular dependencies
- Track re-exports
```

**2. Function/Struct Discovery**
```julia
# Current: grep + manual inspection
# Tree-Sitter: AST-based extraction
- Locate all function definitions
- Extract function signatures
- Map type annotations
- List exported symbols
- Track overloads
```

**3. Cross-Language Symbol Resolution**
```
# Current: Manual mapping across provers
# Tree-Sitter: Unified analysis
For each theorem in Lean4:
  - Find equivalent in Dafny
  - Locate Coq formalization
  - Map Agda proof
  - Track cross-references
```

**4. Integration Point Detection**
```julia
# Current: Manual design
# Tree-Sitter: Automatic identification
- Find integration points in agent code
- Detect shared state usage
- Verify thread safety
- Identify callback patterns
```

**5. Test Coverage Analysis**
```julia
# Current: Manual counting
# Tree-Sitter: Systematic analysis
- Map test cases to functions tested
- Find untested code paths
- Identify test dependencies
- Generate coverage reports
```

---

## Optimal Tree-Sitter Skill Design

### Proposed: `theorem-discovery-analyzer` Skill

**Purpose**: Enable intelligent theorem discovery and verification across plurigrid/asi by analyzing code structure, dependencies, and proof relationships.

**Target Languages** (in priority order):
1. Julia (spectral modules)
2. Lean4 (math library)
3. Python (orchestration scripts)
4. Rust (performance modules)
5. Coq, Agda, Idris (formal verification)

### Architecture

```julia
module TheoremDiscoveryAnalyzer

# Core capabilities
├── Multi-Language Parsing
│   ├── parse_julia_module()
│   ├── parse_lean4_file()
│   ├── parse_python_script()
│   ├── parse_rust_crate()
│   └── parse_formal_proof()
│
├── Symbol Resolution
│   ├── extract_functions()
│   ├── extract_structs()
│   ├── extract_theorems()
│   ├── map_exports()
│   └── resolve_imports()
│
├── Dependency Analysis
│   ├── build_dependency_graph()
│   ├── detect_circular_deps()
│   ├── find_integration_points()
│   └── track_data_flow()
│
├── Cross-Language Linking
│   ├── match_equivalent_theorems()
│   ├── resolve_symbols_across_provers()
│   ├── track_proof_relationships()
│   └── build_unified_index()
│
└── AST-Based Analysis
    ├── find_unused_code()
    ├── analyze_function_calls()
    ├── track_type_annotations()
    └── measure_complexity()

end
```

### Usage Patterns for Spectral Architecture

**1. Agent Module Analysis**
```julia
using TheoremDiscoveryAnalyzer

# Analyze spectral_skills.jl
analysis = analyze_module("spectral_skills.jl")

# Get all exported functions
exports = analysis.exports
# => [:check_system_health, :get_system_gap, :is_system_healthy, ...]

# Find all dependencies
deps = analysis.dependencies
# => [:LinearAlgebra, :Statistics, :Dates]

# Get function signatures
signatures = analysis.functions
# => check_system_health() -> SystemHealthStatus
```

**2. Integration Point Detection**
```julia
# Find where comprehension_discovery uses spectral_skills
integrations = find_integrations(
    from_module="comprehension_discovery.jl",
    to_module="spectral_skills.jl"
)

# Verify integration compatibility
compatibility = verify_integration(integrations)
# Checks: type compatibility, circular deps, thread safety, etc.
```

**3. Cross-Prover Theorem Mapping**
```julia
# Find theorem "GaloisClosure" across all provers
theorem_refs = find_theorem_across_provers("GaloisClosure")
# => [
#   (prover: :Lean4, file: "GaloisDerangement.lean", line: 45),
#   (prover: :Dafny, file: "spi_galois.dfy", line: 170),
#   (prover: :Coq, file: "galois_exponential.v", line: 128),
# ]

# Generate proof equivalence checker
equivalence = verify_theorem_equivalence(theorem_refs)
```

**4. Automatic Documentation Generation**
```julia
# Generate module documentation from code
docs = generate_documentation("agents/", language=:julia)
# Extracts:
# - Function signatures with types
# - Module dependencies
# - Export list
# - Example usage patterns
# - Thread safety notes
```

---

## Integration Strategy

### Phase 1: Minimal Integration (Week 28)

**Goal**: Add tree-sitter for Julia module analysis

```julia
# Simple wrapper around tree-sitter
module TreeSitterJuliaAnalyzer

function analyze_julia_module(path::String)
    # Parse with tree-sitter
    tree = parse_tree(path, language=:julia)

    # Extract symbols
    exports = extract_exports(tree)
    imports = extract_imports(tree)
    functions = extract_functions(tree)
    structs = extract_structs(tree)

    return (
        path=path,
        exports=exports,
        imports=imports,
        functions=functions,
        structs=structs
    )
end

end
```

**Use Cases**:
- Verify all spectral modules have proper exports
- Check for missing docstrings
- Validate type annotations
- Find unused imports

### Phase 2: Extended Integration (Week 29)

**Goal**: Add dependency graph construction

```julia
# Build complete dependency graph
function build_module_graph(root_path::String)
    modules = find_all_modules(root_path)
    graph = dependency_graph()

    for module in modules
        analysis = analyze_julia_module(module)
        for import in analysis.imports
            add_edge!(graph, module, import)
        end
    end

    return graph
end

# Analyze integration compatibility
function verify_integration_chain()
    graph = build_module_graph("agents/")

    # Phase 1 uses: spectral_skills, health_tracking
    # Phase 2 uses: comprehension_discovery (depends on spectral_skills)

    return check_compatibility(graph)
end
```

### Phase 3: Cross-Language Support (Week 30+)

**Goal**: Enable multi-language theorem discovery

```julia
# Unified analysis across 6 provers
function find_theorem_everywhere(theorem_name::String)
    results = MultiProverTheoremIndex()

    # Search in each prover
    results[:lean4] = find_in_lean4(theorem_name)
    results[:dafny] = find_in_dafny(theorem_name)
    results[:coq] = find_in_coq(theorem_name)
    results[:agda] = find_in_agda(theorem_name)
    results[:idris] = find_in_idris(theorem_name)
    results[:stellogen] = find_in_stellogen(theorem_name)

    return results
end
```

---

## Comparison: Manual vs. Tree-Sitter Analysis

### Finding All Functions in a Module

**Manual (Current)**:
```bash
# 1. Read file content
# 2. Search for "function" keyword
# 3. Extract names by pattern matching
# 4. Manually verify signatures
# Time: 5-10 minutes per file
grep -n "^function\|^    function" spectral_skills.jl | head -20
```

**Tree-Sitter (Proposed)**:
```julia
# 1. Parse AST
# 2. Traverse function_definition nodes
# 3. Extract signatures with types
# 4. Verify against actual implementation
# Time: <1 second per file
functions = extract_functions("spectral_skills.jl")
```

### Building Dependency Graph

**Manual**:
```
1. List all imports in spectral_skills.jl
2. List all imports in health_tracking.jl
3. List all imports in comprehension_discovery.jl
4. Draw diagram manually
5. Check for circular dependencies by inspection
Time: 15-30 minutes, error-prone
```

**Tree-Sitter**:
```julia
graph = build_dependency_graph("agents/")
circular_deps = find_circular_dependencies(graph)
```
**Time: <100ms, guaranteed correctness**

### Verifying Integration

**Manual**:
```
1. Check that comprehension_discovery imports spectral_skills
2. Find SystemHealthStatus struct definition
3. Verify it's used in comprehension_discovery
4. Check for type mismatches manually
5. Run tests to catch errors
Time: 20-40 minutes
```

**Tree-Sitter**:
```julia
integration = verify_integration(
    from="comprehension_discovery.jl",
    to="spectral_skills.jl"
)
# Checks:
# ✓ Import exists
# ✓ All types match
# ✓ No circular dependencies
# ✓ All functions available
# Time: <200ms
```

---

## Skill Design Recommendations

### 1. **Scope** (Focused, Not Over-Engineered)

**DO**:
- Focus on Julia modules (primary language)
- Support Lean4 for theorem verification
- Basic Python script analysis
- Export/import verification

**DON'T**:
- Don't build full multi-language parser from scratch
- Don't try to understand semantics deeply
- Don't replace existing linters/type checkers
- Don't support all 6 provers initially

### 2. **Integration Points** (How We'll Actually Use It)

```julia
# 1. Verify module health on each commit
@hook pre-commit:
  analyze_module("agents/comprehension_discovery.jl")
  verify_exports_complete()
  check_for_unused_imports()

# 2. Build dependency graph before testing
@setup tests:
  build_dependency_graph()
  verify_no_circular_deps()
  check_integration_points()

# 3. Generate integration docs automatically
@release:
  generate_module_documentation()
  extract_function_signatures()
  create_integration_guide()
```

### 3. **Performance Targets**

| Operation | Manual | Tree-Sitter | Target |
|-----------|--------|-------------|--------|
| Analyze 1 module | 5-10 min | <100ms | <500ms |
| Build dep graph | 15-30 min | <100ms | <1s |
| Verify integration | 20-40 min | <200ms | <2s |
| Find function | 1-5 min | <50ms | <500ms |
| Check exports | 5 min | <30ms | <200ms |

### 4. **Success Metrics**

- **Correctness**: 100% match with manual analysis
- **Speed**: >100x faster than manual methods
- **Adoption**: Used in every Phase 2+ stage
- **Reliability**: Zero false negatives in integration checks

---

## Implementation Roadmap

### Week 28.1 (Immediate)

```
Create tree-sitter-julia-analyzer skill
├── Basic Julia parsing
├── Function extraction
├── Export/import detection
└── Unit tests (9 tests, 100% pass)
```

### Week 28.2

```
Integrate into Phase 2 Stage 3
├── Verify bidirectional-navigator compatibility
├── Check resource tracking patterns
└── Generate integration docs
```

### Week 28.3

```
Add Lean4 support
├── Parse .lean files
├── Extract theorem definitions
├── Map to proof implementations
└── Cross-check with Dafny proofs
```

### Week 29+

```
Multi-prover unification
├── Unified theorem index
├── Cross-prover symbol resolution
├── Proof equivalence verification
└── Automated theorem mapping
```

---

## Files to Create/Modify

### New Files

```
.codex/skills/tree-sitter-analyzer/
├── SKILL.md                      (Skill manifest)
├── tree_sitter_analyzer.jl       (Core module)
├── julia_analyzer.jl             (Julia language support)
├── lean4_analyzer.jl             (Lean4 language support)
├── test_tree_sitter_analyzer.jl  (Tests)
└── examples/
    ├── analyze_module_example.jl
    ├── verify_integration_example.jl
    └── build_graph_example.jl
```

### Modified Files

```
agents/
├── spectral_skills.jl            (Add @export comments)
├── health_tracking.jl            (Add @export comments)
├── comprehension_discovery.jl    (Add @export comments)
└── Create .jl.tree-sitter file   (Optional AST cache)
```

---

## Comparison: Why Tree-Sitter Over Other Tools

| Tool | Pros | Cons | Our Use |
|------|------|------|---------|
| **grep** | Fast, simple | No AST, false positives | Current baseline |
| **Julia Reflection** | Accurate, native | Runtime only, no imports | Not helpful |
| **Treemacs/LSP** | IDE integrated | Not scriptable, IDE-only | Not portable |
| **Tree-Sitter** | ✅ Fast, ✅ Accurate, ✅ Scriptable | Learning curve | **OPTIMAL** |
| **Custom Parser** | Full control | Maintenance burden | Overkill |

---

## Risk Mitigation

### Risk 1: Over-Engineering

**Mitigation**:
- Start with Julia support only
- Add languages incrementally
- No attempt to understand semantics
- Use tree-sitter as structured parser, not analyzer

### Risk 2: False Positives in Integration Checks

**Mitigation**:
- Always verify with actual imports/exports
- Fall back to manual verification on ambiguity
- Log all integration checks
- Run tests to catch integration issues

### Risk 3: Complexity in Multi-Language Support

**Mitigation**:
- Lean4 only initially (unified .lean syntax)
- Don't attempt Dafny/Coq parsing early
- Use separate modules per language
- Degrade gracefully if unsupported language encountered

---

## Conclusion

**Tree-Sitter Integration Strategy:**

1. **Start Small** - Julia module analysis first
2. **High Value** - Automates 50+ hours of manual work
3. **Low Risk** - Used only for verification, not code generation
4. **Scalable** - Extends naturally to more languages
5. **Practical** - Directly supports Phases 2-4 implementation

**Optimal Timeline**: Implement Week 28 (1-2 hour implementation), deploy for Phase 2 Stage 3.

**Expected Impact**:
- ✅ 100x speedup on module analysis
- ✅ Eliminate manual integration verification errors
- ✅ Automate documentation generation
- ✅ Enable intelligent theorem cross-referencing
- ✅ Foundation for future multi-prover unification

---

**Generated**: December 22, 2025
**Status**: Design Complete - Ready for Implementation
