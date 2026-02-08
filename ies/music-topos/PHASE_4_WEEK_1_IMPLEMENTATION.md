# Phase 4 Week 1: Deploy Tree-sitter MCP Server

**Status**: IN PROGRESS
**Week**: 1 / 5
**Goal**: Extract 50-200 code patterns from music-topos codebase
**Effort**: 5-10 hours
**Deliverable**: `pattern_dump.json` with all extracted patterns

---

## Immediate Tasks (This Week)

### Task 1: Review Architecture Documents (2 hours)
- ✅ **AGENT_ORAMA_TREESITTER_MCP_INTEGRATION.md** Sections 1-3
  - Executive summary of Phase 4
  - System architecture overview (5-layer design)
  - Code distillation pipeline (3 stages)
- ✅ **PHASE_4_QUICKSTART_GUIDE.md**
  - Quick implementation sequence
  - Step-by-step code examples
- ✅ **PHASE_4_DATA_FLOW_ARCHITECTURE.md**
  - Complete system data flow (Phase 1→4)
  - Component dependencies

### Task 2: Prepare Development Environment (2 hours)

#### 2.1 Install Tree-sitter Dependencies
```bash
# Install tree-sitter Python bindings
pip install tree-sitter

# Install tree-sitter language parsers
pip install tree-sitter-languages

# Verify installation
python3 -c "from tree_sitter import Language, Parser; print('✓ tree-sitter ready')"
```

#### 2.2 Check Existing MCP Server Structure
- **File**: `mcp_unified_server.py` (production MCP server)
- **Structure**:
  - KnowledgeAPI (perception tools)
  - ColorAPI (action tools)
  - ColorableSexpAPI (code visualization)
  - UnifiedMCPServer (integration)
- **Next**: Add TreeSitterAPI for code analysis

#### 2.3 Set Up Python Environment
```bash
cd /Users/bob/ies/music-topos

# Create virtualenv if needed
python3 -m venv venv_phase4
source venv_phase4/bin/activate

# Install requirements
pip install tree-sitter tree-sitter-languages
pip install pytest  # For testing patterns
```

### Task 3: Deploy Tree-sitter MCP (3 hours)

#### Option A: Use Existing Open-Source Implementation (RECOMMENDED - Faster)
```bash
# Clone Zed Industries tree-sitter MCP reference
git clone https://github.com/zed-industries/zed-mcp-server-tree-sitter /tmp/tree_sitter_mcp

# Review structure
ls -la /tmp/tree_sitter_mcp/

# Integrate key functions into mcp_unified_server.py
```

#### Option B: Implement Custom MCP Wrapper (More Control)
Create `src/tree_sitter_mcp_integration.py`:

**Key Components:**
1. TreeSitterMCPAPI class
2. 25+ analysis tools:
   - File operations (list_files, get_file, file_metadata)
   - AST extraction (get_ast, get_ast_node)
   - Symbol extraction (get_symbols, get_functions, get_classes)
   - Pattern matching (find_patterns, run_query)
   - Dependency tracking (get_dependencies)
   - Complexity analysis (analyze_complexity)

#### Example Tool Implementations:

```python
class TreeSitterMCPAPI:
    """Tree-sitter integration for code analysis."""

    def __init__(self):
        from tree_sitter import Language, Parser
        self.parser = Parser()
        # Load Ruby parser (primary language for music-topos)
        self.ruby_language = Language('/path/to/tree-sitter-ruby.so', 'ruby')
        self.parser.set_language(self.ruby_language)

    def extract_ast(self, file_path: str) -> Dict[str, Any]:
        """Extract AST from Ruby file."""
        with open(file_path, 'r') as f:
            code = f.read()

        tree = self.parser.parse(code.encode())
        return {
            'file': file_path,
            'ast': self._tree_to_dict(tree.root_node),
            'language': 'ruby',
            'node_count': self._count_nodes(tree.root_node)
        }

    def extract_symbols(self, file_path: str) -> Dict[str, List[str]]:
        """Extract function/class names from Ruby file."""
        with open(file_path, 'r') as f:
            code = f.read()

        tree = self.parser.parse(code.encode())
        symbols = {
            'functions': [],
            'classes': [],
            'modules': [],
            'constants': []
        }

        # Walk AST and extract symbol definitions
        self._walk_symbols(tree.root_node, symbols)
        return symbols

    def find_patterns(self, pattern_query: str) -> List[Dict[str, Any]]:
        """Find code patterns matching tree-sitter query."""
        # pattern_query: tree-sitter pattern syntax
        # Returns: all matching nodes with context
        pass

    def analyze_complexity(self, file_path: str) -> Dict[str, int]:
        """Analyze code complexity metrics."""
        return {
            'cyclomatic_complexity': 0,  # TODO: calculate
            'nesting_depth': 0,          # TODO: calculate
            'function_count': 0,         # TODO: extract
            'lines_of_code': 0          # TODO: count
        }
```

### Task 4: Register Project with Tree-sitter

```python
# In tree_sitter_mcp_integration.py
project = {
    'name': 'music-topos',
    'root': '/Users/bob/ies/music-topos',
    'files': {
        'ruby': [],           # All .rb files
        'clojure': [],        # All .clj files
        'julia': [],          # All .jl files
    },
    'config': {
        'parse_timeout_ms': 5000,
        'max_ast_depth': 20,
        'compression': 'snappy'
    }
}

# Load all files
def scan_project(root_dir):
    for root, dirs, files in os.walk(root_dir):
        for file in files:
            if file.endswith('.rb'):
                project['files']['ruby'].append(os.path.join(root, file))
            elif file.endswith('.clj'):
                project['files']['clojure'].append(os.path.join(root, file))
            elif file.endswith('.jl'):
                project['files']['julia'].append(os.path.join(root, file))
```

---

## Week 1 Implementation Steps

### Step 1: Prepare Code Analysis Infrastructure
**Time: 3 hours**

```bash
# Create src/agents/tree_sitter_mcp_server.py (400 LOC)
# - TreeSitterMCPAPI class
# - 25+ analysis tool implementations
# - File scanning and caching

# Create tests/test_tree_sitter_mcp.py (200 LOC)
# - Test AST extraction
# - Test symbol extraction
# - Test pattern matching
# - Test complexity analysis
```

### Step 2: Integrate into Unified MCP Server
**Time: 2 hours**

```python
# Update mcp_unified_server.py
# Add to UnifiedMCPServer.__init__:
from src.agents.tree_sitter_mcp_server import TreeSitterMCPAPI
self.tree_sitter = TreeSitterMCPAPI()

# Add tools to get_tools():
{
    "name": "list_project_files",
    "description": "List all files in music-topos project",
    "input_schema": {...}
},
{
    "name": "extract_ast",
    "description": "Extract AST from a file",
    "input_schema": {...}
},
# ... 23 more tools
```

### Step 3: Test Tree-sitter Server
**Time: 1 hour**

```bash
# Run unit tests
pytest tests/test_tree_sitter_mcp.py -v

# Manual testing
python3 -c "
from src.agents.tree_sitter_mcp_server import TreeSitterMCPAPI
api = TreeSitterMCPAPI()

# Test on lib/group_theory.rb
ast = api.extract_ast('/Users/bob/ies/music-topos/lib/group_theory.rb')
print('AST nodes:', ast['node_count'])

symbols = api.extract_symbols('/Users/bob/ies/music-topos/lib/group_theory.rb')
print('Functions:', symbols['functions'])
"
```

### Step 4: Extract Code Patterns
**Time: 2 hours**

**Goal**: Extract 50-200 raw code patterns from music-topos

```python
# Create scripts/extract_patterns.py (200 LOC)
import json
from src.agents.tree_sitter_mcp_server import TreeSitterMCPAPI

api = TreeSitterMCPAPI()

patterns = {
    'technical_innovation': [],      # Optimization, algorithms
    'collaborative_work': [],        # Agent coordination
    'philosophical_reflection': [],  # Type definitions, ontology
    'network_building': [],          # Dependencies, integration
    'musical_creation': [],          # Audio synthesis, DSP
    'synthesis': []                  # Pipeline composition
}

# Step 1: Scan all Ruby files
for rb_file in api.list_ruby_files():
    print(f"Scanning {rb_file}...")

    # Extract AST
    ast = api.extract_ast(rb_file)

    # Extract symbols
    symbols = api.extract_symbols(rb_file)

    # Classify patterns by content
    with open(rb_file, 'r') as f:
        code = f.read()

    # Technical innovation
    if 'def' in code and ('optimize' in code or 'algorithm' in code):
        patterns['technical_innovation'].append({
            'file': rb_file,
            'type': 'function_definition',
            'size': len(code.split('\n')),
            'snippet': code[:500]
        })

    # ... classify other patterns

# Save to JSON
with open('/Users/bob/ies/music-topos/patterns/pattern_dump.json', 'w') as f:
    json.dump(patterns, f, indent=2)

print(f"✓ Extracted {sum(len(p) for p in patterns.values())} patterns")
```

### Step 5: Verify Pattern Extraction
**Time: 1 hour**

```bash
# Run pattern extraction
python3 scripts/extract_patterns.py

# Verify output
jq '.technical_innovation | length' patterns/pattern_dump.json

# Check sample patterns
jq '.collaborative_work[0]' patterns/pattern_dump.json
```

---

## Success Criteria (Week 1)

- ✅ Tree-sitter dependencies installed
- ✅ MCP server extended with 25+ tools
- ✅ Project registered in tree-sitter system
- ✅ 50-200 patterns extracted
- ✅ Patterns categorized by leitmotif type
- ✅ `pattern_dump.json` generated
- ✅ All tests passing
- ✅ Ready for Week 2 (3-stage distillation)

---

## Files to Create This Week

```
src/agents/
├── tree_sitter_mcp_server.py        (400 LOC)
│   ├── TreeSitterMCPAPI class
│   ├── 25+ analysis tools
│   └── File scanning/caching
│
├── tree_sitter_integration.clj       (Optional: Clojure binding)
│
└── pattern_extractor.py              (100 LOC)
    ├── Pattern classification
    └── JSON serialization

tests/
├── test_tree_sitter_mcp.py           (200 LOC)
│   ├── Test AST extraction
│   ├── Test symbol extraction
│   └── Test pattern matching
│
└── test_pattern_extraction.py        (150 LOC)
    ├── Test categorization
    └── Test JSON serialization

scripts/
├── extract_patterns.py               (200 LOC)
│   └── Main pattern extraction script
│
└── verify_patterns.py                (100 LOC)
    └── Pattern validation & statistics

patterns/
└── pattern_dump.json                 (Output file)
    └── 50-200 extracted patterns

Updated:
└── mcp_unified_server.py             (Add TreeSitterMCPAPI)
```

---

## Technical Specifications

### Tree-sitter Tool Categories (25+ tools)

**File Operations (4 tools)**
- list_project_files() → all files in project
- get_file(path) → file contents
- get_file_metadata(path) → size, modified time, type
- file_exists(path) → boolean

**AST Extraction (5 tools)**
- extract_ast(file) → full AST
- get_ast_node(file, line, col) → node at position
- get_node_type(file, line, col) → node type
- get_node_text(file, line, col) → node source code
- walk_ast(file) → all nodes in depth-first order

**Symbol Extraction (6 tools)**
- get_symbols(file) → all symbols
- get_functions(file) → function definitions
- get_classes(file) → class definitions
- get_imports(file) → import statements
- get_constants(file) → constant definitions
- get_methods(file) → method definitions

**Pattern Matching (4 tools)**
- find_patterns(pattern_query) → matching nodes
- run_query(query_string) → arbitrary tree-sitter query
- find_similar_code(snippet) → similar patterns
- pattern_statistics() → pattern frequency

**Analysis (4 tools)**
- analyze_complexity(file) → cyclomatic complexity, nesting depth
- get_dependencies(file) → file dependencies
- calculate_metrics(file) → LOC, function count, etc.
- find_dead_code(file) → unused functions/variables

**Leitmotif Classification (2 tools)**
- classify_leitmotif(code) → semantic category
- extract_all_leitmotifs() → all patterns by category

---

## Estimated Timeline

| Task | Time | Status |
|------|------|--------|
| Review documentation | 2h | Ready |
| Prepare environment | 2h | Ready |
| Deploy tree-sitter | 3h | Ready |
| Extract patterns | 2h | Ready |
| Verify output | 1h | Ready |
| **Total Week 1** | **10h** | **Ready to Begin** |

---

## Failure Mitigations

| Risk | Mitigation |
|------|-----------|
| Tree-sitter parsing fails on Ruby | Use proven open-source implementation (Zed Industries) |
| Pattern extraction too slow | Implement parallel processing, cache ASTs |
| JSON file too large | Use jsonlines format, compress with gzip |
| Pattern categorization inaccurate | Use LLM to verify classifications in Week 2 |
| Memory overflow on large files | Stream processing, set max file size limits |

---

## Next Phase (Week 2)

Once `pattern_dump.json` is complete:
1. Input 50-200 patterns to 3-stage distillation pipeline
2. Stage 1: Abstraction (remove specificity)
3. Stage 2: Clustering (group by similarity)
4. Stage 3: Consolidation (create 8-15 MCPs)
5. Output: `consolidated_mcps.json`

See **PHASE_4_WEEK_2_IMPLEMENTATION.md** for details.

---

**Session Start**: 2025-12-21
**Week 1 Deadline**: 2025-12-28
**Next Review**: PHASE_4_WEEK_2_IMPLEMENTATION.md

