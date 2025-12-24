# Agent-o-rama + Tree-sitter MCP Integration Architecture

**Status**: Design Phase Ready for Implementation
**Date**: 2025-12-21
**Target Completion**: Phase 4 (Agent Training + Network Analysis)

---

## Executive Summary

This document outlines the complete integration of tree-sitter code analysis with Agent-o-rama's cognitive surrogate training system, leveraging the existing music-topos MCP infrastructure and GF(3) skill coordination framework.

**Key Integration Points**:
1. **Tree-sitter MCP Server**: Code analysis infrastructure exposing 25+ analysis tools
2. **Agent-o-rama Integration**: Training cognitive surrogates with code distillation patterns
3. **GF(3) Skill System**: Triadic skill loading with polarity-balanced coordination
4. **Phase 2 Entropy Framework**: Preventing mode collapse during agent training
5. **Ramalabs Growth Model**: Iterative refinement through production traces and datasets

**Expected Outcomes**:
- Automated extraction of 50+ distinct code patterns from music-topos repository
- Cognitive surrogate trained on @barton's interaction style + GitHub coding patterns
- GF(3)-conserved skill loading with deterministic color-based agent agreement
- Entropy-monitored training preventing degenerate collapse
- Self-improving system through production feedback loops

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                   INTEGRATED SYSTEM                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌──────────────┐         ┌───────────────────┐                 │
│  │ PHASE 2:     │         │ PHASE 3:          │                 │
│  │ Colorable    │         │ 5D Pattern        │                 │
│  │ Music Topos  │────────→│ Extraction        │                 │
│  │              │         │                   │                 │
│  │ • Entropy    │         │ • Temporal        │                 │
│  │ • Leitmotifs │         │ • Topic           │                 │
│  │ • Colors     │         │ • Interaction     │                 │
│  │ • Music      │         │ • Learning        │                 │
│  │              │         │ • Network         │                 │
│  └──────────────┘         └─────────┬─────────┘                 │
│                                    │                             │
│         ┌──────────────────────────┤                             │
│         │                          │                             │
│    ┌────▼──────────────┐   ┌──────▼────────────────┐            │
│    │ TREE-SITTER MCP   │   │ AGENT-O-RAMA          │            │
│    │ CODE ANALYSIS     │   │ COGNITIVE SURROGATE   │            │
│    │                   │   │                       │            │
│    │ ├─ AST Parsing    │   │ ├─ Agent Training     │            │
│    │ ├─ Symbol Extract │   │ ├─ Multi-agent Coord  │            │
│    │ ├─ Dependency Mgmt│   │ ├─ Skill Distribution │            │
│    │ ├─ Complexity Ana │   │ ├─ Entropy Monitoring │            │
│    │ ├─ Pattern Match  │   │ └─ Learning Feedback  │            │
│    │ └─ Code Distill   │   └───────────┬───────────┘            │
│    └────┬──────────────┘               │                         │
│         │                              │                         │
│         └──────────────┬───────────────┘                         │
│                        │                                         │
│              ┌─────────▼──────────┐                              │
│              │ GF(3) SKILL        │                              │
│              │ COORDINATION       │                              │
│              │                    │                              │
│              │ ├─ RED (+1)        │                              │
│              │ │  Generator Skills│                              │
│              │ ├─ GREEN (0)       │                              │
│              │ │  Coordinator Skil│                              │
│              │ └─ BLUE (-1)       │                              │
│              │    Validator Skills│                              │
│              └────────┬───────────┘                              │
│                       │                                          │
│            ┌──────────▼──────────┐                               │
│            │ DETERMINISTIC COLOR │                               │
│            │ COORDINATION        │                               │
│            │ (Gay.rs agreement)  │                               │
│            └─────────────────────┘                               │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
```

---

## 1. CODE DISTILLATION PIPELINE

### 1.1 Three-Stage Extraction Process

The code distillation pipeline extracts reusable patterns from source code to train agent-o-rama:

```
┌────────────────────────────────────────────────────────────────┐
│ STAGE 1: ABSTRACTION                                           │
│                                                                │
│ Input: Raw code patterns (functions, classes, workflows)      │
│                                                                │
│ Process:                                                       │
│  1. Parse with tree-sitter → AST + symbols                   │
│  2. Extract code structure + logic flow                       │
│  3. Identify key parameters (≤3 per pattern)                  │
│  4. Remove example-specific details                           │
│  5. Generalize implementation logic                           │
│                                                                │
│ Output: Abstracted_MCP (generalized pattern)                  │
│         Example:                                              │
│         - Function name, signature                            │
│         - Parameters: [input_type, config, options]           │
│         - Logic: parameterized implementation                 │
│         - Complexity metrics                                  │
└────────────────────────────────────────────────────────────────┘
        │
        ▼
┌────────────────────────────────────────────────────────────────┐
│ STAGE 2: CLUSTERING                                            │
│                                                                │
│ Input: {Abstracted_MCPs} (50-200 patterns)                    │
│                                                                │
│ Process:                                                       │
│  1. Semantic analysis: What problem does each solve?          │
│  2. Capability clustering: Group by application domain        │
│  3. Redundancy detection: Merge similar patterns              │
│  4. Dependency analysis: Pattern call graphs                  │
│  5. Create functional groups (8-15 clusters)                  │
│                                                                │
│ Output: Cluster_MCPs (grouped patterns)                        │
│         Example clusters:                                      │
│         - "Data Processing" (10 patterns)                      │
│         - "Musical Analysis" (8 patterns)                      │
│         - "Graph Operations" (12 patterns)                     │
│         - "Entropy Calculation" (5 patterns)                   │
│         - "Color Generation" (3 patterns)                      │
└────────────────────────────────────────────────────────────────┘
        │
        ▼
┌────────────────────────────────────────────────────────────────┐
│ STAGE 3: CONSOLIDATION                                         │
│                                                                │
│ Input: Cluster_MCPs (functional groups)                        │
│                                                                │
│ Process:                                                       │
│  1. Merge similar implementations within cluster              │
│  2. Create general-purpose version with unified params        │
│  3. Add parameter validation and error handling               │
│  4. Generate FastMCP-compatible Python code                   │
│  5. Create test cases for each consolidated MCP               │
│                                                                │
│ Output: Final_MCPs (8-15 MCP tools)                           │
│         Each ready for:                                        │
│         - Direct use by agents                                │
│         - Parameter adaptation                                │
│         - Zero-shot transfer to new tasks                      │
│         - Composition with other MCPs                         │
└────────────────────────────────────────────────────────────────┘
```

### 1.2 Implementation Architecture

```
tree-sitter MCP Server
    │
    ├─ File I/O Layer
    │  ├─ list_files (pattern-based)
    │  ├─ get_file (with caching)
    │  └─ get_file_metadata
    │
    ├─ AST Analysis Layer
    │  ├─ get_ast (configurable depth)
    │  ├─ get_symbols (functions, classes, imports)
    │  ├─ analyze_complexity (cyclomatic + lines)
    │  ├─ analyze_project (structural overview)
    │  └─ get_dependencies (import graph)
    │
    ├─ Pattern Extraction Layer
    │  ├─ find_similar_code (detect duplicates)
    │  ├─ find_usage (symbol tracking)
    │  ├─ run_query (custom tree-sitter queries)
    │  └─ build_query (query composition)
    │
    └─ Distillation Layer
       ├─ extract_abstracted_patterns
       ├─ cluster_by_semantics
       ├─ consolidate_mcps
       └─ generate_mcp_code

                    ↓ (50-200 raw patterns)
                    ↓
        Code Distillation Engine
                    ↓
                    ├─ LLM abstraction
                    ├─ LLM clustering
                    ├─ LLM consolidation
                    ↓
                    ↓ (8-15 MCP tools)
                    ↓
        Agent-o-rama Tool Registry
                    ↓
        Agent Training + Execution
```

---

## 2. TREE-SITTER MCP SERVER DESIGN

### 2.1 Core Capabilities

**25+ Analysis Tools Across 5 Categories:**

#### A. Project Management (4 tools)
```
register_project_tool(path, name?, description?)
  → Register new codebase for analysis

list_projects_tool()
  → Show all registered projects

remove_project_tool(name)
  → Unregister project

analyze_project(project, scan_depth=3)
  → Get project structure overview
```

#### B. File Operations (4 tools)
```
list_files(project, pattern?, max_depth?, extensions?)
  → Find files matching criteria
  → Example: list_files("music-topos", "**/*.clj", max_depth=2)

get_file(project, path, max_lines?, start_line=0)
  → Retrieve file content with optional line limiting

get_file_metadata(project, path)
  → Get file stats (size, modified time, language)

find_text(project, pattern, file_pattern?, case_sensitive=false, use_regex=false)
  → Full-text search with regex support
```

#### C. AST Analysis (6 tools)
```
get_ast(project, path, max_depth=5, include_text=true)
  → Parse file to Abstract Syntax Tree
  → Output: Nested JSON with node types, positions, text

get_node_at_position(project, path, row, column)
  → Find AST node at specific location

get_symbols(project, path, symbol_types?)
  → Extract functions, classes, imports, variables
  → Returns: {functions: [...], classes: [...], imports: [...]}

analyze_complexity(project, path)
  → Calculate cyclomatic complexity + metrics

get_dependencies(project, path)
  → Identify all imports/requires with paths

get_node_types(language)
  → Show all node types for language (documentation)
```

#### D. Query & Search (8 tools)
```
run_query(project, query, file_path?, language?, max_results=100)
  → Execute tree-sitter query on project
  → Returns: Matching nodes with positions

get_query_template_tool(language, template_name)
  → Get pre-built query (e.g., "functions", "classes")

list_query_templates_tool(language?)
  → Show available query templates

build_query(language, patterns[], combine="or")
  → Combine multiple query patterns

adapt_query(query, from_language, to_language)
  → Port query between languages

find_similar_code(project, snippet, language?, threshold=0.8, max_results=10)
  → Detect code duplication

find_usage(project, symbol, file_path?, language?)
  → Track symbol usage across codebase

find_text(project, pattern, file_pattern?, case_sensitive=false, use_regex=false, context_lines=2)
  → Pattern matching with context
```

#### E. Utility (3 tools)
```
list_languages()
  → Show available language parsers (31+ languages)

check_language_available(language)
  → Verify specific language support

clear_cache(project?, file_path?)
  → Clear parse tree cache for performance reset
```

### 2.2 Language Support Matrix

```
Primary Languages (40+ supported):
├─ Dynamic:  JavaScript, TypeScript, Python, Ruby, PHP
├─ Compiled: Go, Rust, Java, C/C++, C#
├─ Functional: Clojure, Scheme, Lisp, Haskell, OCaml
├─ Domain:  SQL, JSON, YAML, TOML, HTML
└─ Special:  Bash, Dockerfile, Makefile, Terraform
```

### 2.3 Query Example: Extract Leitmotifs from Code

Using tree-sitter queries to find semantic patterns:

```clojure
;; Query 1: Find "technical-innovation" patterns
;; Looking for: Performance optimization, algorithm improvements
(query-pattern
  '(find-text project
     "(defn .*-fast\\|defn .*-optimiz\\|recur\\|loop\\|lazy)"
     :use_regex true
     :context_lines 5))

;; Query 2: Find "collaborative-work" patterns
;; Looking for: Multi-agent coordination, shared state
(query-pattern
  '(run-query project
     "(call_expression (identifier) @func)"
     :file_path "src/agents/"
     :language "clojure"))

;; Query 3: Find "philosophical-reflection" patterns
;; Looking for: Type definitions, ontology code
(query-pattern
  '(find-text project
     "(defprotocol\\|defrecord\\|deftype\\|schema\\|spec)"
     :use_regex true))

;; Query 4: Find "network-building" patterns
;; Looking for: Dependencies, imports, connections
(query-pattern
  '(get-dependencies project "src/agents/phase_2_integration.clj"))

;; Query 5: Find "musical-creation" patterns
;; Looking for: Audio/music generation code
(query-pattern
  '(find-text project
     "(synth\\|overtone\\|supercollider\\|midi\\|audio)"
     :use_regex true
     :file_pattern "**/*.clj"))

;; Query 6: Find "synthesis" patterns
;; Looking for: Integration, unification, bridge code
(query-pattern
  '(find-text project
     "(->\\|compose\\|merge\\|integrate\\|pipeline)"
     :use_regex true))
```

---

## 3. AGENT-O-RAMA INTEGRATION SPECIFICATION

### 3.1 Agent Module Architecture

```java
// File: src/agents/CognitiveAgentModule.java

public class CognitiveAgentModule extends RamaModule {

  @Override
  public void define(Setup setup, Topology topology) {

    // Define agent objects (shared resources)
    AgentObjectDefinition agentObjects = new AgentObjectDefinition()
      .object("tree-sitter-mcp", TreeSitterMCP.class)
      .object("llm-client", LLMClient.class)          // Claude API
      .object("color-generator", GayRSColorGen.class) // Deterministic colors
      .object("entropy-monitor", EntropyMonitor.class)
      .object("skill-loader", SkillLoader.class);     // GF(3) skills

    // Define cognitive surrogate agent
    topology.newAgent("cognitive-surrogate")
      .state()
        .field("agent-name", String.class)
        .field("skill-set", List.class)               // [+1, 0, -1] skills
        .field("entropy-baseline", Double.class)
        .field("pattern-memory", Map.class)           // Learned patterns
        .field("trace-history", List.class)           // Agent execution traces

      // Node 1: Initialize surrogate with personality
      .node("initialize", "analyze-codebase",
        (AgentNode node, CognitiveInitRequest req) -> {

          // Load three canonical triads (GF(3)-balanced)
          SkillSet skills = loadTriadicSkills(
            req.agentName(),
            req.personalityVector()
          );

          node.state().setField("skill-set", skills);
          node.state().setField("agent-name", req.agentName());
          node.emit("analyze-codebase", "skills", skills);
        })

      // Node 2: Analyze codebase with tree-sitter
      .node("analyze-codebase", "extract-patterns",
        (AgentNode node, SkillSet skills) -> {

          TreeSitterMCP mcp = node.object("tree-sitter-mcp");

          // Run 6 parallel queries (leitmotif patterns)
          List<PatternGroup> patterns = new ArrayList<>();

          patterns.add(mcp.query(TECHNICAL_INNOVATION_QUERY));
          patterns.add(mcp.query(COLLABORATIVE_WORK_QUERY));
          patterns.add(mcp.query(PHILOSOPHICAL_REFLECTION_QUERY));
          patterns.add(mcp.query(NETWORK_BUILDING_QUERY));
          patterns.add(mcp.query(MUSICAL_CREATION_QUERY));
          patterns.add(mcp.query(SYNTHESIS_QUERY));

          node.emit("extract-patterns", "patterns", patterns);
        })

      // Node 3: Extract MCPs via distillation
      .node("extract-patterns", "consolidate-mcps",
        (AgentNode node, List<PatternGroup> patterns) -> {

          LLMClient llm = node.object("llm-client");

          // Stage 1: Abstract patterns
          List<AbstractedMCP> abstracted = patterns.stream()
            .map(pg -> llm.abstractPattern(pg))
            .collect(toList());

          // Stage 2: Cluster by semantics
          List<ClusteredMCP> clustered = llm.clusterPatterns(abstracted);

          // Stage 3: Consolidate (done in next node)
          node.emit("consolidate-mcps", "clusters", clustered);
        })

      // Node 4: Consolidate MCPs
      .node("consolidate-mcps", "train-surrogate",
        (AgentNode node, List<ClusteredMCP> clusters) -> {

          LLMClient llm = node.object("llm-client");

          List<FinalMCP> consolidated = clusters.stream()
            .map(cm -> llm.consolidateMCP(cm))
            .collect(toList());

          // Generate Python code for each MCP
          Map<String, String> mcpCode = consolidated.stream()
            .collect(toMap(
              FinalMCP::name,
              FinalMCP::generatePythonCode
            ));

          node.emit("train-surrogate", "mcps", mcpCode);
        })

      // Node 5: Train surrogate with entropy monitoring
      .node("train-surrogate", "evaluate",
        (AgentNode node, Map<String, String> mcpCode) -> {

          EntropyMonitor entropy = node.object("entropy-monitor");
          LLMClient llm = node.object("llm-client");

          // Training loop with entropy tracking
          List<TrainingMetrics> metrics = new ArrayList<>();

          for (int epoch = 0; epoch < 10; epoch++) {

            // Sample: Generate agent response
            String response = llm.generateWithMCPs(mcpCode);

            // Measure: 5D entropy of response
            double[] entropies = entropy.measure5D(response);

            // Monitor: Check for mode collapse
            if (entropy.isCollapsing(entropies)) {
              // Recover: Reduce learning rate + restore checkpoint
              entropy.applyRecoveryStrategy();
            }

            metrics.add(new TrainingMetrics(epoch, entropies));
          }

          node.emit("evaluate", "metrics", metrics);
        })

      // Node 6: Evaluate against test set
      .node("evaluate", "complete",
        (AgentNode node, List<TrainingMetrics> metrics) -> {

          GayRSColorGen colorGen = node.object("color-generator");

          // Assign deterministic color to surrogate
          int seed = computeSurrogateSignature(node.state());
          String color = colorGen.colorAt(seed);

          // Log completion
          node.state().setField(
            "trace-history",
            buildTraceRecord(
              node.state(),
              metrics,
              color
            )
          );

          node.emit("complete", "success", true);
        });
  }
}
```

### 3.2 Clojure Integration Alternative

```clojure
;; File: src/agents/cognitive_surrogate.clj

(defmodule CognitiveSurrogateModule

  ;; Agent initialization with triadic skills
  (aor/new-agent "cognitive-surrogate"

    ;; State definition
    (aor/state
      {:agent-name String
       :skill-set SkillSet         ; [+1, 0, -1] balanced
       :entropy-baseline Double
       :pattern-memory Map
       :trace-history List})

    ;; Node 1: Initialize
    (aor/node "initialize" "analyze-codebase"
      (fn [agent-node {agent-name :agent-name personality :personality}]
        (let [skills (load-triadic-skills agent-name personality)]
          (aor/emit! agent-node "analyze-codebase"
            {:skills skills}))))

    ;; Node 2: Analyze codebase
    (aor/node "analyze-codebase" "extract-patterns"
      (fn [agent-node {skills :skills}]
        (let [mcp (aor/object agent-node "tree-sitter-mcp")
              patterns (parallel-query-leitmotifs mcp)]
          (aor/emit! agent-node "extract-patterns"
            {:patterns patterns}))))

    ;; Node 3: Extract MCPs (3-stage distillation)
    (aor/node "extract-patterns" "consolidate-mcps"
      (fn [agent-node {patterns :patterns}]
        (let [llm (aor/object agent-node "llm-client")
              abstracted (map #(llm/abstract-pattern llm %) patterns)
              clustered (llm/cluster-patterns llm abstracted)]
          (aor/emit! agent-node "consolidate-mcps"
            {:clusters clustered}))))

    ;; Node 4: Consolidate MCPs
    (aor/node "consolidate-mcps" "train-surrogate"
      (fn [agent-node {clusters :clusters}]
        (let [llm (aor/object agent-node "llm-client")
              consolidated (mapv #(llm/consolidate-mcp llm %) clusters)]
          (aor/emit! agent-node "train-surrogate"
            {:mcps consolidated}))))

    ;; Node 5: Train with entropy monitoring
    (aor/node "train-surrogate" "evaluate"
      (fn [agent-node {mcps :mcps}]
        (let [entropy (aor/object agent-node "entropy-monitor")
              llm (aor/object agent-node "llm-client")
              metrics (for [epoch (range 10)]
                        (let [response (llm/generate-with-mcps llm mcps)
                              entropies (entropy/measure-5d entropy response)]
                          (when (entropy/is-collapsing? entropy entropies)
                            (entropy/apply-recovery! entropy))
                          {:epoch epoch :entropies entropies}))]
          (aor/emit! agent-node "evaluate"
            {:metrics metrics}))))

    ;; Node 6: Evaluate & complete
    (aor/node "evaluate" "complete"
      (fn [agent-node {metrics :metrics}]
        (let [color-gen (aor/object agent-node "color-generator")
              seed (compute-surrogate-signature (:agent-state agent-node))
              color (color-gen/color-at color-gen seed)]
          (aor/emit! agent-node "complete"
            {:success true :color color}))))))
```

### 3.3 Agent Invocation & Streaming

```clojure
;; Client code for invoking cognitive surrogate

(require '[redplanetlabs.agent-o-rama.api :as aor])

;; Create agent client
(def client (aor/agent-client "cognitive-surrogate"))

;; Invoke with personality vector
(def result (aor/invoke client
  {:agent-name "@barton"
   :personality [0.8 0.6 0.9]  ; Technical, collaborative, philosophical
   :target-entropy 2.85}))

;; Or stream results progressively
(aor/stream result "train-surrogate"
  (fn [all-chunks new-chunks is-reset is-complete]
    (when is-complete
      (println "Training complete: " all-chunks))))

;; Access final trace
(println "Agent trace:" (:trace-history result))
(println "Learned MCPs:" (:mcps result))
```

---

## 4. GF(3) SKILL COORDINATION FRAMEWORK

### 4.1 Triadic Skill Architecture

The existing GF(3) skill system (from `.agents/AGENTS.md`) defines 29 skills organized as **synergistic 3-tuples** with polarity conservation:

```
GF(3) Trit Mapping:
  -1 (MINUS/Blue)   → VALIDATOR role (verify, constrain, reduce)
  0  (ERGODIC/Green) → COORDINATOR role (transport, derive, navigate)
  +1 (PLUS/Red)     → GENERATOR role (create, compose, generate)

Conservation Law: All triads must sum to 0 mod 3
  Example: (-1) + (0) + (+1) ≡ 0 (mod 3) ✓
```

### 4.2 Canonical Triads for Agent Training

**Triad 1: Core System** [Already in place]
```
  three-match (-1)        → Validation/constraint (blue)
  ⊗ unworld (0)          → Coordination (green)
  ⊗ gay-mcp (+1)         → Generation/color (red)
  ─────────────────────────
  Sum = 0 (mod 3) ✓
```

**Triad 2: Analysis & Extraction** [For code distillation]
```
  clj-kondo-3color (-1)   → Code analysis/validation (blue)
  ⊗ tree-sitter (0)       → AST parsing/navigation (green)
  ⊗ distillation (+1)     → MCP generation (red)
  ─────────────────────────
  Sum = 0 (mod 3) ✓
```

**Triad 3: Agent Training** [For surrogate learning]
```
  proofgeneral-narya (-1)  → Proof/constraint checking (blue)
  ⊗ entropia-monitor (0)   → Entropy measurement (green)
  ⊗ agent-o-rama (+1)      → Agent generation (red)
  ─────────────────────────
  Sum = 0 (mod 3) ✓
```

**Triad 4: Skill Loading** [For dynamic skill selection]
```
  slime-lisp (-1)         → REPL constraint (blue)
  ⊗ borkdude (0)          → Code evaluation (green)
  ⊗ cider-clojure (+1)    → Interactive generation (red)
  ─────────────────────────
  Sum = 0 (mod 3) ✓
```

### 4.3 Skill Loading Protocol

```
Dynamic Skill Selection:
  1. Identify task polarity (-1, 0, or +1)
  2. Load compatible triad from skill registry
  3. Invoke skills in order: validator → coordinator → generator
  4. Verify GF(3) conservation throughout
  5. Assign deterministic color from Gay.rs

Example: "Train agent on code patterns" (task = +1/generation)

Step 1: Load (+1) compatible skills
  → Search skills with +1 polarity
  → Find: [agent-o-rama, distillation, cider-clojure, ...]

Step 2: Build valid triad
  → Find (-1) validator: proofgeneral-narya
  → Find (0) coordinator: entropia-monitor
  → Find (+1) generator: agent-o-rama
  → Verify: (-1) + (0) + (+1) = 0 (mod 3) ✓

Step 3: Execute in sequence
  → Run: proofgeneral-narya (validate task)
  → Run: entropia-monitor (setup monitoring)
  → Run: agent-o-rama (execute training)

Step 4: Color assignment
  → Compute seed from execution
  → Get deterministic color from Gay.rs
  → Use color for: agent identity, trace visualization, agreement protocol
```

### 4.4 Deterministic Color-Based Agent Agreement

The system uses **Gay.rs deterministic color generation** to ensure agent agreement without explicit communication:

```
Protocol: "Implicit Coordination via Color"

Given: Same seed → same color (always)

Use Case: Multiple agents analyzing same code pattern

Step 1: Agents independently analyze code
  Agent A: tree-sitter analyze "entropy_metrics.clj" → AST
  Agent B: tree-sitter analyze "entropy_metrics.clj" → AST
  Agent C: tree-sitter analyze "entropy_metrics.clj" → AST

Step 2: Agents compute independent signatures
  Agent A: hash(AST) = 0x4271 → seed = 4271
  Agent B: hash(AST) = 0x4271 → seed = 4271
  Agent C: hash(AST) = 0x4271 → seed = 4271

Step 3: Agents request colors
  Agent A: color_at(4271) → #A855F7 (purple)
  Agent B: color_at(4271) → #A855F7 (purple)
  Agent C: color_at(4271) → #A855F7 (purple)

Result: AGREEMENT WITHOUT COMMUNICATION
  All three agents assigned same color to same pattern
  No network round-trips required
  Coordination is implicit in mathematics
```

---

## 5. ENTROPY MONITORING & MODE COLLAPSE PREVENTION

Integration of Phase 2 entropy framework with agent training:

### 5.1 5-Dimensional Entropy During Training

```python
# File: src/agents/entropy_monitoring.py

class EntropySurrogateMonitor:
    """Monitor agent training for mode collapse using 5D entropy"""

    def measure_5d(self, agent_output):
        """
        Measure 5 entropy dimensions of agent output

        Returns:
          {
            'topic_entropy': 3.4,           # Semantic diversity
            'mode_entropy': 2.5,            # Interaction type diversity
            'temporal_entropy': 1.9,        # Temporal pattern diversity
            'network_entropy': 2.1,         # Dependency diversity
            'length_entropy': 1.8,          # Expression length diversity
          }
        """
        pass

    def detect_collapse_risk(self, entropy_history):
        """
        Detect mode collapse via slope analysis

        Mode collapse signature:
          - Slope < -0.1 bits/epoch (entropy decreasing)
          - Variance < 0.05 bits (converging to few patterns)
          - Entropy < 1.0 bits (dominated by single mode)

        Returns:
          {
            'is_collapsing': True/False,
            'slope': -0.15,  # bits/epoch
            'risk_level': 'CRITICAL'|'HIGH'|'MEDIUM'|'LOW',
            'dominant_mode': 'technical_innovation'  # Which pattern dominates
          }
        """
        pass

    def apply_recovery_strategy(self):
        """
        Recover from imminent mode collapse:

        1. Reduce learning rate (LR → LR * 0.5)
        2. Restore checkpoint (return to recent good state)
        3. Inject diversity (add counter-examples to training)
        4. Rebalance entropy targets (reweight loss function)
        5. Resume training
        """
        pass

    def compute_diversity_loss(self, agent_state):
        """
        Diversity loss function: Penalize low entropy

        L_diversity = Σ(max(0, 1.5 - entropy[i])) / 5

        When agent entropy < 1.5, incur penalty
        Pushes agent toward maintaining 5D diversity
        """
        pass

class IntegrationExample:
    def train_surrogate_with_monitoring(self, agent, training_data):
        """
        Full training loop with entropy monitoring

        Expected behavior:
          - Epoch 0-3: Entropy rises (learning patterns)
          - Epoch 4-7: Entropy stabilizes (convergence)
          - Epoch 8-10: Entropy maintained (learned model)

        Expected entropy ranges:
          - Topic: 2.5-3.5 bits (good diversity)
          - Mode: 1.8-2.6 bits (multiple interaction types)
          - Temporal: 1.2-2.0 bits (non-repetitive)
          - Network: 1.8-2.8 bits (mixed dependencies)
          - Length: 1.2-2.0 bits (varied expression)

        If any dimension drops significantly, apply recovery
        """

        entropy_monitor = EntropySurrogateMonitor()

        for epoch in range(10):

            # Generate output from agent
            output = agent.generate(training_data)

            # Measure 5D entropy
            entropies = entropy_monitor.measure_5d(output)

            # Check for collapse
            if entropy_monitor.detect_collapse_risk([entropies]):
                print(f"COLLAPSE RISK at epoch {epoch}!")
                entropy_monitor.apply_recovery_strategy()

            # Compute loss with diversity penalty
            base_loss = compute_task_loss(output)
            div_loss = entropy_monitor.compute_diversity_loss(agent.state)
            total_loss = base_loss + 0.1 * div_loss

            # Backprop
            agent.update(total_loss)

            print(f"Epoch {epoch}: entropy={entropies}, loss={total_loss}")

        return agent
```

### 5.2 Expected Entropy Trajectories

```
Healthy Training (No Mode Collapse):
┌─────────────────────────────────────────────────────────────┐
│ Entropy (bits)                                              │
│                                                             │
│ 3.5 │                                                       │
│     │     ╱─────────────────────────────────────┐          │
│ 3.0 │    ╱                                       │          │
│     │   ╱                                        │          │
│ 2.5 │  ╱                                         │          │
│     │ ╱                                          │          │
│ 2.0 │▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔▔│▔│ ← Stable
│     │ (Learning phase)        (Convergence)  │  │
│ 1.5 └─────────────────────────────────────────┼──┘
│       0    2    4    6    8    10 Epoch
└─────────────────────────────────────────────────────────────┘

Mode Collapse (To Prevent):
┌─────────────────────────────────────────────────────────────┐
│ Entropy (bits)                                              │
│                                                             │
│ 3.5 │                                                       │
│     │    ╱╲                                                 │
│ 3.0 │   ╱  ╲                                                │
│     │  ╱    ╲                                               │
│ 2.5 │ ╱      ╲                                              │
│     │         ╲                                             │
│ 2.0 │          ╲ ← Collapse detected                       │
│     │           ╲                                           │
│ 1.5 │            ╲_____                                     │
│     │                  ╲___                                 │
│ 1.0 │                      ╲___ ← Only 1-2 modes dominate  │
│     │                           ╲___                        │
│ 0.5 └────────────────────────────────╲──────────────────────│
│       0    2    4    6    8    10 Epoch
└─────────────────────────────────────────────────────────────┘
       RECOVERY TRIGGERED AT EPOCH 4
       LR reduced, checkpoint restored, training resumed
```

---

## 6. INTEGRATION WITH EXISTING PHASE 2 SYSTEMS

### 6.1 Data Flow from Phase 2 → Phase 3 → Agent Training

```
Phase 2 Outputs (Colorable Music Topos):
  ├─ Optimal Gay seed (deterministic agreement)
  ├─ 6 Leitmotif tags + confidences
  ├─ 340+ interaction colors (HSV)
  ├─ Musical timeline (MIDI events)
  └─ Entropy baseline (5D vector)
         │
         ▼
Phase 3 Processing (5D Pattern Extraction):
  ├─ Temporal patterns (how interactions cluster over time)
  ├─ Topic patterns (subject evolution)
  ├─ Interaction patterns (mode distribution)
  ├─ Learning patterns (skill growth)
  └─ Network patterns (relationship dynamics)
         │
         ▼
Phase 4 - Agent Training (Agent-o-rama + Tree-sitter):
  ├─ Tree-sitter analyzes code patterns
  ├─ 3-stage distillation (abstraction → clustering → consolidation)
  ├─ LLM generates MCP tools (8-15 tools)
  ├─ Agent-o-rama trains cognitive surrogate
  ├─ Entropy monitoring prevents mode collapse
  ├─ GF(3) skill loading coordinates training
  └─ Deterministic colors assign agent identity
         │
         ▼
Phase 5-7 Outputs:
  ├─ Trained cognitive surrogate (mimics @barton patterns)
  ├─ Skill trajectories (how agent learns)
  ├─ Network influence map (interperspectival analysis)
  └─ Complete trace history (interpretable execution)
```

### 6.2 Using Phase 2 Entropy Baseline in Agent Training

```clojure
;; From phase_2_integration.clj (Phase 2)
(def entropy-baseline
  {:topic 3.42
   :mode 2.31
   :temporal 1.87
   :network 2.15
   :length 1.52
   :overall-health "HEALTHY"})

;; In agent training (Phase 4)
(defn initialize-agent-with-entropy-targets
  [entropy-baseline personality-vector]

  ;; Use Phase 2 entropy as baseline for surrogate
  ;; Agent should maintain ≥90% of baseline entropy during training

  (let [targets {:topic (:topic entropy-baseline)
                 :mode (:mode entropy-baseline)
                 :temporal (:temporal entropy-baseline)
                 :network (:network entropy-baseline)
                 :length (:length entropy-baseline)}]

    ;; During training, if agent entropy drops below 90% of target
    ;; trigger recovery mechanism
    {:entropy-targets targets
     :minimum-acceptable (multiply-by-constant targets 0.9)
     :recovery-threshold 0.85
     :collapse-risk-detection :enabled}))
```

### 6.3 Extending Phase 2 Leitmotifs with Code Patterns

```
Phase 2 Leitmotifs (Interaction patterns):
  ├─ Technical-innovation (hue 0-60°)
  ├─ Collaborative-work (hue 60-120°)
  ├─ Philosophical-reflection (hue 120-180°)
  ├─ Network-building (hue 180-240°)
  ├─ Musical-creation (hue 240-300°)
  └─ Synthesis (hue 300-360°)

Extended with Phase 4 Code Patterns:
  ├─ Technical-innovation
  │   ├─ Performance optimization (algorithms, parallelization)
  │   ├─ Bug fixes (error handling, edge cases)
  │   └─ Architecture improvements (modularization, refactoring)
  │
  ├─ Collaborative-work
  │   ├─ Multi-agent coordination (message passing, state sharing)
  │   ├─ API design (interface specification, contracts)
  │   └─ Testing infrastructure (test suites, fixtures)
  │
  ├─ Philosophical-reflection
  │   ├─ Type system design (protocols, schemas, ontology)
  │   ├─ Documentation (comments, docstrings, theory)
  │   └─ Design decisions (architectural notes, rationale)
  │
  ├─ Network-building
  │   ├─ Dependency management (imports, module organization)
  │   ├─ Integration layers (bridges, adapters, API clients)
  │   └─ Configuration management (settings, parameters, tuning)
  │
  ├─ Musical-creation
  │   ├─ Audio synthesis (signal processing, DSP)
  │   ├─ Real-time systems (timing-critical code)
  │   └─ Creative tools (generative algorithms, randomization)
  │
  └─ Synthesis
      ├─ Pipeline composition (data flow integration)
      ├─ Unified interfaces (abstraction layers)
      └─ Cross-domain bridges (category theory, formal methods)
```

---

## 7. RAMALABS GROWTH STRATEGY IMPLEMENTATION

### 7.1 Iterative Refinement Loop

Following Ramalabs philosophy of self-instrumentation and feedback loops:

```
ITERATION 1: Initial Training
  ├─ Collect interaction data (@barton Bluesky + GitHub)
  ├─ Run Phase 2: Entropy analysis + colorization
  ├─ Extract Phase 3: 5D patterns
  ├─ Distill Phase 4: Tree-sitter MCPs (50-200 patterns)
  ├─ Train: Cognitive surrogate on extracted patterns
  ├─ Evaluate: Test on held-out interactions
  └─ Metrics: Accuracy, mode collapse risk, entropy stability
       │
       ▼ (Save all traces to DuckDB)

ITERATION 2: Production Execution
  ├─ Deploy trained surrogate to production
  ├─ Run surrogate on new interactions
  ├─ Capture execution traces
  ├─ Log: LLM calls, token counts, tool usage, timing
  ├─ Measure: Response quality via human evaluation
  └─ Identify: Failure cases, low-entropy patterns
       │
       ▼ (Add failures to training dataset)

ITERATION 3: Refinement
  ├─ Add failed predictions to dataset
  ├─ Re-run distillation on expanded code base
  ├─ Extract new MCPs addressing failure modes
  ├─ Fine-tune surrogate on failure cases
  ├─ A/B test: New version vs baseline
  └─ Deploy improved version
       │
       ▼ (Loop continues, system improves)
```

### 7.2 Observability & Metrics Collection

```python
# File: src/agents/agent_observability.py

class AgentObservabilityFramework:
    """
    Collect detailed metrics on agent-o-rama execution
    following Ramalabs self-instrumentation principles
    """

    def record_training_trace(self, epoch, agent_state):
        """
        Log complete training state for time-travel debugging

        Captures:
          - Agent state snapshot
          - 5D entropy measurements
          - LLM call details (model, tokens, latency)
          - Tool invocations (tree-sitter, color generation)
          - Skill loading decisions (which GF(3) triad used)
          - Color assignments (Gay.rs seed, deterministic result)
          - Timing (wall-clock latency per operation)
        """
        trace = {
            'epoch': epoch,
            'timestamp': current_timestamp(),
            'agent_state': agent_state.serialize(),
            'entropy_5d': entropy_monitor.measure_5d(agent_state),
            'llm_calls': [
                {
                    'model': 'claude-opus-4.5',
                    'input_tokens': n_tokens_in,
                    'output_tokens': n_tokens_out,
                    'latency_ms': elapsed_ms,
                    'operation': 'abstract_pattern|cluster|consolidate',
                }
            ],
            'tool_usage': {
                'tree_sitter_queries': count,
                'color_generations': count,
                'skill_loads': count,
            },
            'skills_loaded': ['clj-kondo-3color', 'tree-sitter', 'distillation'],
            'colors_assigned': [
                {'seed': 4271, 'color': '#A855F7', 'pattern': 'entropy_metrics'}
            ],
            'metrics': {
                'mode_collapse_risk': 'LOW',
                'diversity_loss': 0.1234,
                'task_loss': 0.5678,
                'total_loss': 0.6912,
            }
        }

        # Store in DuckDB
        duckdb.insert('agent_training_traces', trace)

        return trace

    def generate_iteration_report(self, iteration_num):
        """
        Generate comprehensive report on iteration performance

        Output:
          - Accuracy metrics vs baseline
          - Entropy stability analysis
          - Mode collapse incidents (if any)
          - Skill utilization distribution
          - LLM cost analysis
          - Recommended improvements
        """

        # Query all traces from this iteration
        traces = duckdb.query(
            f"SELECT * FROM agent_training_traces WHERE iteration = {iteration_num}"
        )

        report = {
            'iteration': iteration_num,
            'timestamp': current_timestamp(),
            'num_epochs': len(traces),
            'accuracy': compute_accuracy(traces),
            'entropy_stability': compute_stability(traces),
            'mode_collapse_incidents': count_collapse_events(traces),
            'skill_distribution': analyze_skill_usage(traces),
            'llm_cost': compute_llm_spend(traces),
            'recommendations': [
                'Increase learning rate (entropy too stable)',
                'Add more training examples for low-entropy domains',
                'Explore alternative skill triads',
            ]
        }

        return report

    def export_dataset_for_next_iteration(self, failed_predictions):
        """
        Create dataset for next iteration based on failures

        Takes: List of (input, expected_output, actual_output)
        Returns: JSONL file ready for re-training
        """

        dataset = []
        for (inp, expected, actual) in failed_predictions:
            dataset.append({
                'input': inp,
                'expected_output': expected,
                'actual_output': actual,
                'error_type': classify_error(expected, actual),
                'suggested_mcp': extract_needed_capability(expected),
            })

        with open(f'training_data_iteration_{iteration}.jsonl', 'w') as f:
            for row in dataset:
                f.write(json.dumps(row) + '\n')

        return dataset
```

### 7.3 Production Deployment Pipeline

```bash
#!/bin/bash
# File: scripts/deploy_agent_iteration.sh

# PHASE 4: Agent Training & Deployment
# Implements Ramalabs iterative refinement loop

ITERATION=$1

echo "==== AGENT-O-RAMA ITERATION $ITERATION ===="

# Step 1: Extract code patterns with tree-sitter
echo "Step 1: Extract code patterns..."
clj -M:agents \
  -e "(require '[agents.tree-sitter-mcp :as ts])
      (ts/register-project \"/Users/bob/ies/music-topos\")
      (ts/extract-all-patterns)"

# Step 2: Distill MCPs (abstraction → clustering → consolidation)
echo "Step 2: Distill MCPs..."
python3 src/agents/code_distillation.py \
  --input patterns.json \
  --output mcps_iteration_$ITERATION.json \
  --num-clusters 12

# Step 3: Train cognitive surrogate with agent-o-rama
echo "Step 3: Train surrogate..."
java -cp target/agent-o-rama.jar \
  com.redplanetlabs.agent_o_rama.CognitiveSurrogateModule \
  --iteration $ITERATION \
  --mcps mcps_iteration_$ITERATION.json \
  --entropy-baseline 2.85 \
  --epochs 10

# Step 4: Evaluate on test set
echo "Step 4: Evaluate..."
clj -M:agents \
  -e "(require '[agents.evaluation :as eval])
      (eval/evaluate-surrogate
        :iteration $ITERATION
        :test-set \"test_interactions.edn\")"

# Step 5: Generate iteration report
echo "Step 5: Generate report..."
python3 src/agents/observability.py \
  --iteration $ITERATION \
  --generate-report true

# Step 6: Export dataset for next iteration (if needed)
echo "Step 6: Export dataset..."
python3 src/agents/dataset_export.py \
  --iteration $ITERATION \
  --include-failures true \
  --output training_data_iteration_$((ITERATION+1)).jsonl

# Step 7: Optional: Deploy to production if metrics good
if [ "$(python3 scripts/check_metrics.py $ITERATION)" = "GOOD" ]; then
  echo "Metrics acceptable. Deploying to production..."
  rama deploy \
    --module target/agent-o-rama.jar \
    --cluster music-topos-agents \
    --version iteration-$ITERATION
fi

echo "==== ITERATION $ITERATION COMPLETE ===="
```

---

## 8. IMPLEMENTATION ROADMAP

### 8.1 Phase 4 Implementation Tasks

**Week 1: Tree-sitter MCP Server**
- [ ] Deploy tree-sitter MCP server (use `wrale/mcp-server-tree-sitter`)
- [ ] Register music-topos project
- [ ] Implement 6 leitmotif query patterns
- [ ] Test AST analysis on existing code
- [ ] Extract initial 50+ code patterns

**Week 2: Code Distillation Pipeline**
- [ ] Implement Stage 1: Pattern abstraction (LLM-based)
- [ ] Implement Stage 2: Pattern clustering (semantic grouping)
- [ ] Implement Stage 3: MCP consolidation (Python generation)
- [ ] Generate first set of 8-15 MCPs
- [ ] Test MCP functionality

**Week 3: Agent-o-rama Integration**
- [ ] Set up Agent-o-rama project (fork from `redplanetlabs/agent-o-rama`)
- [ ] Implement `CognitiveSurrogateModule` (Java)
- [ ] Create agent nodes for: init → analyze → extract → train → evaluate
- [ ] Integrate tree-sitter MCP as agent object
- [ ] Integrate entropy monitoring in training loop

**Week 4: GF(3) Skill Coordination**
- [ ] Implement triadic skill loader (Java/Clojure)
- [ ] Define 4 canonical triads for agent training
- [ ] Implement deterministic color assignment (Gay.rs integration)
- [ ] Test skill loading and color coordination
- [ ] Verify GF(3) conservation

**Week 5: Testing & Deployment**
- [ ] Unit tests for each component
- [ ] Integration test: end-to-end Phase 4 execution
- [ ] Entropy monitoring validation
- [ ] Production deployment pipeline
- [ ] First iteration complete

### 8.2 Validation Checklist

```
PHASE 4 COMPLETION CRITERIA:

Tree-sitter MCP:
  ☐ MCP server running with 25+ tools available
  ☐ All 6 leitmotif patterns extracted from code
  ☐ 50+ code patterns identified and categorized
  ☐ AST parsing working for Clojure, Ruby, Python

Code Distillation:
  ☐ Stage 1 abstraction producing 50+ abstracted patterns
  ☐ Stage 2 clustering producing 8-15 semantic groups
  ☐ Stage 3 consolidation producing executable MCPs
  ☐ Generated MCPs have passing tests

Agent-o-rama Integration:
  ☐ Cognitive surrogate module compiles and runs
  ☐ Agent training loop executes 10 epochs
  ☐ MCP tools accessible in training nodes
  ☐ Agent produces meaningful output

GF(3) Skill System:
  ☐ 4 canonical triads implemented and balanced
  ☐ Triadic skill loading working correctly
  ☐ Deterministic colors assigned to patterns
  ☐ Color consistency verified (same seed → same color)

Entropy Monitoring:
  ☐ 5D entropy measured correctly
  ☐ Mode collapse detection working
  ☐ Recovery strategy implemented
  ☐ No uncontrolled entropy decay during training

Production Ready:
  ☐ All unit tests passing
  ☐ Integration tests passing
  ☐ Deployment script working
  ☐ Observability metrics captured to DuckDB
  ☐ Iteration report generated
```

---

## 9. KEY DESIGN DECISIONS

### 9.1 Why This Architecture?

| Component | Choice | Reason |
|-----------|--------|--------|
| **Code Analysis** | Tree-sitter MCP | 40+ languages, AST accuracy, incremental parsing |
| **Code Distillation** | LLM-based 3-stage | Self-contained, generalizable, zero-shot transfer |
| **Agent Framework** | Agent-o-rama | Rama cluster support, JVM-native, tracing built-in |
| **Skill Coordination** | GF(3) + Gay.rs | Deterministic agreement, no network overhead, mathematical elegance |
| **Entropy Monitoring** | 5D measurement | Captures all interaction dimensions, prevents degenerate collapse |
| **Growth Model** | Ramalabs iterative | Production feedback loops, continuous improvement, self-instrumentation |

### 9.2 Failure Modes & Mitigations

| Failure Mode | Mitigation |
|--------------|-----------|
| **Mode collapse** | Entropy monitoring + diversity loss + recovery strategy |
| **Skill triads unbalanced** | GF(3) conservation check before loading |
| **Agent disagreement** | Deterministic color-based coordination (same input → same color) |
| **Code distillation loses semantics** | Multi-stage (abstraction → clustering → consolidation) |
| **Training divergence** | Checkpoint restoration + learning rate reduction |

---

## 10. EXPECTED OUTCOMES & METRICS

### 10.1 Phase 4 Deliverables

**Artifacts**:
- Tree-sitter MCP server (25+ tools, 31 languages)
- Code distillation pipeline (Python scripts)
- Agent-o-rama module (Java/Clojure)
- GF(3) skill coordinator
- Entropy monitoring framework
- Deployment & observability scripts

**Data**:
- 50-200 extracted code patterns (JSON)
- 8-15 consolidated MCPs (Python code)
- Agent training traces (DuckDB)
- Iteration reports (JSON)
- Cognitive surrogate checkpoint

**Quality Metrics**:
- Tree-sitter accuracy: >95% AST parsing
- Code distillation efficiency: >85% pattern consolidation
- Agent training stability: entropy drop <10% at convergence
- Skill loading correctness: 100% GF(3) conservation
- Production readiness: All tests passing

### 10.2 Expected Success Criteria

```
✓ Cognitive surrogate trained and deployable
✓ Learns @barton's interaction patterns (>80% accuracy)
✓ Maintains 5D entropy diversity throughout training
✓ Uses extracted MCPs effectively (>60% tool utilization)
✓ Produces deterministically colored outputs (same input → same color)
✓ Can be iteratively improved via production feedback

Ready for Phase 5: Network analysis & interperspectival views
```

---

## 11. NEXT STEPS

**Immediate Actions**:
1. ✅ Research & understand agent-o-rama (DONE)
2. ✅ Research & understand tree-sitter MCP (DONE)
3. ✅ Design integration architecture (DONE - this document)
4. **Deploy tree-sitter MCP server** (NEXT)
5. **Implement code distillation pipeline** (NEXT)
6. **Build agent-o-rama module** (NEXT)
7. **Run Phase 4 training iteration** (NEXT)

**Success Definition**:
System can train a cognitive surrogate on extracted code patterns, maintain entropy diversity, coordinate skill loading via GF(3), and iteratively improve through production feedback loops.

---

**Document Version**: 1.0
**Status**: Ready for Implementation
**Date**: 2025-12-21
**Author**: Claude Code

Generated with comprehensive research and architectural design for Phase 4 of the music-topos cognitive surrogate project.
