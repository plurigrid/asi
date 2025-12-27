# Phase 4: Agent-o-rama + Tree-sitter MCP Quick Start

**Status**: Ready for Immediate Implementation
**Complexity**: High (but well-structured)
**Estimated Effort**: 4-5 weeks (iterative)

---

## The Big Picture (One Minute Read)

```
You have:
  ✓ Phase 1: Data pipeline (interaction collection)
  ✓ Phase 2: Colorable music topos (entropy + colors + sound)
  ✓ Phase 3 designed: 5D pattern extraction framework
  ✓ Existing MCP server (implemented but not deployed)
  ✓ GF(3) skill system (29 skills, mathematically balanced)

You need:
  → Deploy tree-sitter MCP for code analysis
  → Distill code patterns into 8-15 reusable MCPs (3-stage pipeline)
  → Train cognitive surrogate with agent-o-rama
  → Monitor training with 5D entropy to prevent mode collapse
  → Coordinate skill loading with GF(3) + deterministic colors

Result:
  → Cognitive surrogate that mimics @barton's patterns
  → Trained via code distillation (not raw training data)
  → Self-improving through production feedback loops
```

---

## Implementation Sequence (What to Do First)

### Step 1: Deploy Tree-sitter MCP Server (Days 1-3)

**Option A: Use existing open-source implementation** (Recommended)
```bash
# Install NPM package
npm install @nendo/tree-sitter-mcp

# Or use GitHub implementation
git clone https://github.com/wrale/mcp-server-tree-sitter
cd mcp-server-tree-sitter
cargo build --release
```

**Option B: Implement custom MCP wrapper** (More control)
```python
# File: src/agents/tree_sitter_mcp_server.py

from mcp.server import Server
from tree_sitter import Language, Parser
import os

class TreeSitterMCPServer:
    def __init__(self):
        self.projects = {}
        self.parsers = self._load_parsers()

    def register_project(self, path, name=None):
        """Register codebase for analysis"""
        self.projects[name or os.path.basename(path)] = path
        return {"status": "registered", "project": name}

    def analyze_codebase(self, project_name):
        """Extract all symbols and patterns"""
        project_path = self.projects[project_name]
        results = []

        for root, dirs, files in os.walk(project_path):
            for file in files:
                if file.endswith(('.clj', '.rb', '.py', '.js')):
                    filepath = os.path.join(root, file)
                    ast = self.parse_file(filepath)
                    symbols = self.extract_symbols(ast)
                    results.append({
                        'file': filepath,
                        'symbols': symbols,
                        'ast': ast
                    })

        return results

    def extract_leitmotif_patterns(self, project_name):
        """Extract 6 semantic pattern types"""
        patterns = {
            'technical-innovation': self._find_optimization_code,
            'collaborative-work': self._find_agent_coordination,
            'philosophical-reflection': self._find_type_definitions,
            'network-building': self._find_dependencies,
            'musical-creation': self._find_audio_code,
            'synthesis': self._find_pipeline_code,
        }

        results = {}
        for pattern_name, finder_func in patterns.items():
            results[pattern_name] = finder_func(project_name)

        return results

    # Implement pattern detection methods...
    def _find_optimization_code(self, project_name):
        """Find performance optimization patterns"""
        pass

    def _find_agent_coordination(self, project_name):
        """Find multi-agent code patterns"""
        pass

    # ... etc
```

**Validation**: After deployment, verify:
```bash
# Test basic functionality
curl -X POST http://localhost:3000/register-project \
  -H "Content-Type: application/json" \
  -d '{"path": "/Users/bob/ies/music-topos", "name": "music-topos"}'

# Expected response:
# {"status": "registered", "project": "music-topos"}

# List extracted patterns
curl http://localhost:3000/analyze/music-topos/patterns
```

### Step 2: Implement Code Distillation Pipeline (Days 4-7)

**Core Implementation** (Python):
```python
# File: src/agents/code_distillation_pipeline.py

from anthropic import Anthropic

class CodeDistillationPipeline:

    def __init__(self):
        self.client = Anthropic()
        self.all_messages = []

    # STAGE 1: Abstraction
    def abstract_pattern(self, pattern_code, pattern_name):
        """
        Convert raw code to abstracted MCP

        Removes:
          - Example-specific details
          - Concrete variable names
          - Specific data

        Preserves:
          - Core logic and structure
          - Parameter signature
          - Complexity characteristics
        """

        prompt = f"""You are an expert at code pattern abstraction.

Given this code pattern (from {pattern_name}):

```
{pattern_code}
```

Please abstract this to a general-purpose Model Context Protocol (MCP) by:

1. Identify the core algorithm/logic (3-5 key steps)
2. Extract 1-3 critical parameters that make this reusable
3. Remove example-specific details
4. Create a generalized version

Output JSON:
{{
  "pattern_name": "string",
  "core_logic": ["step 1", "step 2", "step 3"],
  "parameters": [
    {{"name": "param1", "type": "type1", "description": "..."}}
  ],
  "generalized_code": "abstract pseudocode",
  "use_cases": ["use case 1", "use case 2"],
  "complexity": "O(...)"
}}"""

        self.all_messages.append({
            "role": "user",
            "content": prompt
        })

        response = self.client.messages.create(
            model="claude-opus-4.5",
            max_tokens=2000,
            messages=self.all_messages
        )

        abstracted = response.content[0].text
        self.all_messages.append({
            "role": "assistant",
            "content": abstracted
        })

        return abstracted

    # STAGE 2: Clustering
    def cluster_patterns(self, abstracted_patterns):
        """
        Group 50-200 patterns into 8-15 semantic clusters

        Identifies:
          - Common application domains
          - Overlapping functionality
          - Dependency relationships
        """

        patterns_summary = "\n".join([
            f"- {p['pattern_name']}: {p['use_cases']}"
            for p in abstracted_patterns
        ])

        prompt = f"""You are an expert at code organization.

Given these abstracted patterns:

{patterns_summary}

Please cluster them into functional groups by:

1. Identifying semantic similarities
2. Finding shared application domains
3. Detecting dependency relationships
4. Creating descriptive cluster names

Output JSON:
{{
  "clusters": [
    {{
      "cluster_name": "string",
      "description": "what this cluster does",
      "patterns": ["pattern1", "pattern2"],
      "shared_functionality": "how they relate",
      "suggested_mcp_name": "consolidated_name"
    }}
  ]
}}"""

        self.all_messages.append({"role": "user", "content": prompt})

        response = self.client.messages.create(
            model="claude-opus-4.5",
            max_tokens=3000,
            messages=self.all_messages
        )

        clustered = response.content[0].text
        self.all_messages.append({
            "role": "assistant",
            "content": clustered
        })

        return clustered

    # STAGE 3: Consolidation
    def consolidate_mcp(self, cluster):
        """
        Merge cluster patterns into single MCP tool

        Creates:
          - Unified parameter schema
          - General-purpose implementation
          - FastMCP-compatible Python code
          - Test cases
        """

        prompt = f"""You are an expert at creating reusable tools.

Given this cluster of patterns:

{cluster}

Please create a consolidated MCP (Model Context Protocol) tool that:

1. Merges all patterns into one general-purpose tool
2. Unifies parameters across all patterns
3. Handles all use cases in the cluster
4. Provides clear, intuitive interface

Generate FastMCP-compatible Python code:

```python
from fastmcp.core import tools

@tools.tool
def {cluster['suggested_mcp_name']}(
    input_data: str,
    mode: str = 'default',
    options: dict = None
) -> dict:
    '''
    {cluster['cluster_name']}: {cluster['description']}

    Modes: {', '.join(['mode1', 'mode2'])}
    '''
    # Implementation
    pass
```

Also provide:
- Test cases (3-5 examples)
- Error handling strategies
- Performance characteristics"""

        self.all_messages.append({"role": "user", "content": prompt})

        response = self.client.messages.create(
            model="claude-opus-4.5",
            max_tokens=2000,
            messages=self.all_messages
        )

        consolidated = response.content[0].text
        self.all_messages.append({
            "role": "assistant",
            "content": consolidated
        })

        return consolidated

    def run_full_pipeline(self, raw_patterns):
        """Execute 3-stage distillation end-to-end"""

        print("=" * 60)
        print("CODE DISTILLATION PIPELINE")
        print("=" * 60)

        # Stage 1
        print("\n[Stage 1] ABSTRACTION")
        abstracted = []
        for i, pattern in enumerate(raw_patterns, 1):
            print(f"  Abstracting pattern {i}/{len(raw_patterns)}: {pattern['name']}")
            result = self.abstract_pattern(pattern['code'], pattern['name'])
            abstracted.append(json.loads(result))

        print(f"✓ Abstracted {len(abstracted)} patterns")

        # Stage 2
        print("\n[Stage 2] CLUSTERING")
        clustered = self.cluster_patterns(abstracted)
        clusters = json.loads(clustered)['clusters']
        print(f"✓ Created {len(clusters)} semantic clusters")

        # Stage 3
        print("\n[Stage 3] CONSOLIDATION")
        mcps = []
        for i, cluster in enumerate(clusters, 1):
            print(f"  Consolidating cluster {i}/{len(clusters)}: {cluster['cluster_name']}")
            mcp_code = self.consolidate_mcp(cluster)
            mcps.append({'cluster': cluster['cluster_name'], 'code': mcp_code})

        print(f"✓ Generated {len(mcps)} MCP tools")

        return {'abstracted': abstracted, 'clusters': clusters, 'mcps': mcps}
```

**Usage**:
```python
pipeline = CodeDistillationPipeline()

# Extract raw patterns from tree-sitter
raw_patterns = tree_sitter_mcp.extract_all_patterns('music-topos')

# Run full distillation
result = pipeline.run_full_pipeline(raw_patterns)

# Save MCPs
with open('mcps_consolidated.json', 'w') as f:
    json.dump(result, f, indent=2)
```

### Step 3: Set Up Agent-o-rama Module (Days 8-12)

**Simplest Path: Use provided examples**

```bash
# Clone agent-o-rama
git clone https://github.com/redplanetlabs/agent-o-rama
cd agent-o-rama

# Create music-topos agent module
mkdir modules/music-topos-surrogate
cp examples/* modules/music-topos-surrogate/

# Edit: modules/music-topos-surrogate/AgentModule.java
# Add nodes: initialize → analyze → extract → train → evaluate
```

**Core Structure** (Clojure version is simpler):
```clojure
;; File: modules/music-topos-surrogate/core.clj

(defmodule CognitiveSurrogateModule

  (aor/new-agent "cognitive-surrogate"

    (aor/state
      {:agent-name String
       :entropy-baseline Double
       :skill-set List
       :pattern-memory Map})

    ;; 6-node pipeline: init → analyze → extract → consolidate → train → evaluate

    (aor/node "initialize" "analyze-codebase" ...)
    (aor/node "analyze-codebase" "extract-patterns" ...)
    (aor/node "extract-patterns" "consolidate-mcps" ...)
    (aor/node "consolidate-mcps" "train-surrogate" ...)
    (aor/node "train-surrogate" "evaluate" ...)
    (aor/node "evaluate" "complete" ...)))
```

### Step 4: Integrate Entropy Monitoring (Days 13-15)

**Minimal Implementation**:
```python
# File: src/agents/entropy_monitor_for_training.py

def monitor_training(agent_outputs, entropy_baseline):
    """
    Monitor 5D entropy during agent training

    If entropy drops >10% → trigger recovery
    If entropy stable → training is working
    """

    entropy_history = []

    for epoch, output in enumerate(agent_outputs):
        # Measure 5D entropy
        entropies = measure_5d_entropy(output)

        # Check against baseline
        loss = sum(abs(entropies[i] - entropy_baseline[i])
                   for i in range(5))

        if loss > entropy_baseline_sum * 0.1:
            print(f"⚠️  COLLAPSE RISK at epoch {epoch}")
            # Trigger recovery
            return "RECOVERY_NEEDED"

        entropy_history.append(entropies)

    return "HEALTHY"
```

### Step 5: Deploy & Test (Days 16-20)

**Quick Test Suite**:
```bash
# 1. Test tree-sitter MCP
pytest tests/test_tree_sitter_mcp.py

# 2. Test code distillation
pytest tests/test_code_distillation.py

# 3. Test agent-o-rama module
./gradlew :modules:music-topos-surrogate:test

# 4. Integration test
clj -M:test -e '(test/run-phase-4-integration-test)'

# 5. Deploy to production
rama deploy --module music-topos-agents --cluster production
```

---

## Key Files to Create

```
src/agents/
├── tree_sitter_mcp_server.py      (Code analysis interface)
├── code_distillation_pipeline.py   (3-stage distillation)
├── entropy_monitor_for_training.py (5D entropy + recovery)
├── triadic_skill_loader.py         (GF(3) skill coordination)
├── cognitive_surrogate_module.java (Agent-o-rama module)
├── cognitive_surrogate_core.clj    (Clojure alternative)
└── observability_framework.py      (Trace collection)

tests/
├── test_tree_sitter_mcp.py
├── test_code_distillation.py
├── test_entropy_monitoring.py
└── test_integration_phase_4.py

scripts/
├── deploy_iteration.sh             (Iterative training script)
└── check_metrics.py                (Evaluate performance)
```

---

## Success Metrics

### Immediate (Week 1-2)
- [ ] Tree-sitter MCP server running with 25+ tools
- [ ] 50+ code patterns extracted from music-topos
- [ ] Code distillation pipeline produces 8-15 MCPs

### Mid-term (Week 3-4)
- [ ] Agent-o-rama module compiles and runs
- [ ] Cognitive surrogate trains for 10 epochs
- [ ] Entropy stays within ±10% of baseline

### Final (Week 5)
- [ ] Surrogate produces meaningful outputs (>80% accuracy)
- [ ] All tests passing (100%)
- [ ] Production deployment successful
- [ ] First iteration complete

---

## If You Get Stuck

**Problem: Tree-sitter MCP not responding**
→ Check: Is server running? `ps aux | grep tree-sitter`
→ Fix: Restart server, verify port is open

**Problem: Code distillation too slow**
→ Use: Smaller subset of code first
→ Batch: Process patterns in groups of 10

**Problem: Agent training diverges**
→ Enable: Entropy monitoring (will catch early)
→ Check: Entropy baseline is realistic

**Problem: GF(3) conservation failing**
→ Verify: Skill triads sum to 0 mod 3
→ Debug: Print each skill's polarity

---

## Key Insight: Why This Works

```
Classical approach: Train on raw data
  → 10,000 interactions → neural network
  → Mode collapse risk: HIGH
  → Interpretability: LOW

Music-Topos approach: Extract + Distill + Train
  → 10,000 interactions
  → → Phase 2: Extract colorized patterns
  → → Phase 3: Extract 5D semantic patterns
  → → Phase 4: Distill to 8-15 reusable MCPs
  → → Agent-o-rama: Train on MCPs
  → Mode collapse risk: PREVENTED (entropy monitoring)
  → Interpretability: HIGH (every step traced)
  → Reusability: HIGH (MCPs usable for other tasks)
  → Iterability: HIGH (production feedback loop)
```

---

## Ready? Start With This Command

```bash
cd /Users/bob/ies/music-topos

# Deploy tree-sitter MCP
npm install @nendo/tree-sitter-mcp || git clone https://github.com/wrale/mcp-server-tree-sitter

# Test connectivity
clj -M:agents \
  -e "(require '[agents.tree-sitter-mcp :as ts])
      (println (ts/list-languages))"

# If you see list of 31+ languages → you're ready!
# Proceed to Step 2: Code Distillation Pipeline
```

---

**Status**: Ready to begin Phase 4
**Next**: Deploy tree-sitter MCP server
**Time to First Results**: 5-7 days

Generated: 2025-12-21
