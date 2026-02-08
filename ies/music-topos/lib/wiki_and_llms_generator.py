"""
wiki_and_llms_generator.py

Deep wiki documentation system and LLMs.txt index generator
for Quantum Guitar Galois Derangement World.

Generates:
- MkDocs-compatible wiki structure
- Semantic documentation graphs
- LLMs.txt for LLM model discoverability
- Machine-readable proof index
- Skill documentation
"""

import json
import textwrap
from pathlib import Path
from typing import Dict, List, Any
from datetime import datetime

# ============================================================================
# PART 1: Wiki Structure Generator
# ============================================================================

class WikiGenerator:
    """Generate deep wiki documentation"""

    def __init__(self, project_name: str, version: str = "1.0"):
        self.project_name = project_name
        self.version = version
        self.pages = {}
        self.index = {}

    def add_page(self, path: str, title: str, content: str, metadata: Dict = None) -> None:
        """Add wiki page"""
        self.pages[path] = {
            'title': title,
            'content': content,
            'metadata': metadata or {},
            'path': path
        }
        # Update index
        self.index[path] = {
            'title': title,
            'keywords': self._extract_keywords(content)
        }

    def _extract_keywords(self, content: str) -> List[str]:
        """Extract keywords from content"""
        keywords = []
        # Simple extraction: lines starting with ###
        for line in content.split('\n'):
            if line.startswith('###'):
                keywords.append(line.strip('# '))
        return keywords

    def generate_mkdocs_yml(self) -> str:
        """Generate MkDocs configuration"""
        nav_structure = self._build_nav_tree()

        config = {
            'site_name': self.project_name,
            'theme': 'material',
            'nav': nav_structure,
            'plugins': ['search', 'mermaid2'],
            'markdown_extensions': [
                'pymdownx.arithmatex',
                'pymdownx.superfences',
                'pymdownx.tasklist'
            ]
        }

        return textwrap.dedent(f"""
        # MkDocs Configuration
        # Generated for {self.project_name} v{self.version}

        site_name: {self.project_name}
        theme:
          name: material
          palette:
            scheme: dark
            primary: amber
            accent: deep-orange

        nav:
          - Home: index.md
          - Getting Started: getting_started.md
          - Quantum Guitar:
              - Overview: quantum_guitar/overview.md
              - Phases: quantum_guitar/phases.md
              - Gadgets: quantum_guitar/gadgets.md
              - Proofs: quantum_guitar/proofs.md
          - Hy Language Skill:
              - Overview: hy_skill/overview.md
              - Macros: hy_skill/macros.md
              - HyJAX: hy_skill/hyjax.md
              - Examples: hy_skill/examples.md
          - Proof Systems:
              - PyZX: proofs/pyzx.md
              - HyZX: proofs/hyzx.md
              - Quizx: proofs/quizx.md
          - Mathematics: mathematics/index.md
          - API Reference: api/index.md
          - FAQ: faq.md

        plugins:
          - search
          - mermaid2.0

        markdown_extensions:
          - pymdownx.arithmatex:
              generic: true
          - pymdownx.superfences:
              custom_fences:
                - name: mermaid
                  class: mermaid
                  format: !!python/name:pymdownx.superfences.fence_code_block
          - pymdownx.tasklist:
              custom_checkbox: true
        """).strip()

    def _build_nav_tree(self) -> List:
        """Build navigation tree from pages"""
        nav = []
        sections = {}

        for path, page in self.pages.items():
            # Parse path into sections
            parts = path.split('/')
            if len(parts) == 1:
                nav.append({page['title']: path})
            else:
                section = parts[0]
                if section not in sections:
                    sections[section] = []
                sections[section].append({page['title']: path})

        for section, pages in sorted(sections.items()):
            nav.append({section.title(): pages})

        return nav

    def generate_homepage(self) -> str:
        """Generate wiki homepage"""
        return textwrap.dedent(f"""
        # {self.project_name}

        **Version {self.version}**

        Complete documentation for the Quantum Guitar Galois Derangement World,
        including:
        - Formal proof visualization (PyZX, HyZX, Quizx)
        - Hy language skill with embedded source code
        - Phase-scoped rewrite gadget verification
        - Persistent world state management
        - Deep learning integration

        ## Quick Start

        1. [Installation](getting_started.md)
        2. [Tutorial](quantum_guitar/overview.md)
        3. [Hy Skill Guide](hy_skill/overview.md)
        4. [Proof Systems](proofs/overview.md)

        ## Key Concepts

        ### Quantum Guitar Phases
        - **RED Phase**: Covariant forward rewriting (f(x) ≥ x)
        - **BLUE Phase**: Contravariant backward rewriting (f(x) ≤ x)
        - **GREEN Phase**: Neutral identity (f(x) = x)

        ### Galois Derangement
        Permutations that maximally disrupt Galois connections:
        - No fixed points (classical derangement)
        - Violates adjunction property at every level
        - Discovered perturbatively through phase space mining

        ### Formal Proofs
        Three integrated proof visualization systems:
        - **PyZX**: ZX-calculus diagrams
        - **HyZX**: Hy language ZX proofs
        - **Quizx**: Quantum circuit visualization

        ## Documentation Structure

        ```
        {self.project_name}/
        ├── index.md                  # This page
        ├── getting_started.md        # Installation & setup
        ├── quantum_guitar/           # Phase gadget documentation
        │   ├── overview.md
        │   ├── phases.md            # Phase theory
        │   ├── gadgets.md           # Gadget specifications
        │   └── proofs.md            # Proof generation
        ├── hy_skill/                # Hy language documentation
        │   ├── overview.md
        │   ├── macros.md            # Macro reference
        │   ├── hyjax.md             # JAX integration
        │   └── examples.md          # Code examples
        ├── proofs/                  # Proof system documentation
        │   ├── pyzx.md
        │   ├── hyzx.md
        │   └── quizx.md
        ├── mathematics/             # Mathematical foundations
        │   └── index.md
        ├── api/                     # API reference
        │   └── index.md
        └── faq.md                   # Frequently asked questions
        ```

        ---

        **Last Updated**: {datetime.now().isoformat()}
        """).strip()

    def generate_phases_documentation(self) -> str:
        """Generate phase documentation"""
        return textwrap.dedent("""
        # Quantum Guitar Phases

        ## Overview

        The quantum guitar operates through three phase types, corresponding to
        Girard's linear logic polarities and rewrite gadget semantics.

        ## Phase Types

        ### RED Phase (Polarity = +1)

        **Semantics**: Covariant forward rewriting

        $$f(x) \\geq x$$ for all $x \\in [0, \\tau]$

        **Properties**:
        - Monotone: $x \\leq y \\Rightarrow f(x) \\leq f(y)$
        - Amplification: $f(x) = x(1 + \\text{strength})$
        - Ferromagnetic: System expands/grows

        **Physical Interpretation**:
        - Expansion of harmonic space
        - Increase in complexity/information
        - Forward causality

        **Audio Manifestation**:
        - Rising frequencies
        - Brighter timbre
        - Circle of fifths progressions

        ### BLUE Phase (Polarity = -1)

        **Semantics**: Contravariant backward rewriting

        $$f(x) \\leq x$$ for all $x \\in [0, \\tau]$

        **Properties**:
        - Monotone (inverted): $x \\leq y \\Rightarrow f(x) \\geq f(y)$
        - Contraction: $f(x) = x / (1 + \\text{strength})$
        - Antiferromagnetic: System contracts/simplifies

        **Physical Interpretation**:
        - Contraction of harmonic space
        - Decrease in complexity
        - Backward causality/resolution

        **Audio Manifestation**:
        - Falling frequencies
        - Duller timbre
        - Tritone clusters and dissonance

        ### GREEN Phase (Polarity = 0)

        **Semantics**: Neutral identity

        $$f(x) = x$$ for all $x \\in [0, \\tau]$

        **Properties**:
        - Identity: $f(f(x)) = f(x)$
        - Paramagnetic: System maintains equilibrium
        - Transparency: Phase passes through state unchanged

        **Physical Interpretation**:
        - Equilibrium point
        - Identity verification
        - Phase boundary crossing

        **Audio Manifestation**:
        - Constant frequency (pedal point)
        - Sustained drone
        - Beating patterns (interference)

        ## Phase Transitions

        Phases are ordered causally by timestamp:

        $$\\varphi_1 < \\varphi_2 \\Rightarrow \\text{timestamp}_1 < \\text{timestamp}_2$$

        **Composition Rules**:

        | From | To  | Allowed | Result |
        |------|-----|---------|--------|
        | RED  | RED | ✓       | RED    |
        | RED  | BLUE| ✗       | Error  |
        | RED  | GREEN| ✓      | RED    |
        | BLUE | BLUE| ✓       | BLUE   |
        | BLUE | RED | ✗       | Error  |
        | BLUE | GREEN| ✓      | BLUE   |
        | GREEN| *   | ✓       | *      |
        | *    | GREEN| ✓      | *      |

        ## Temperature Parameter (τ)

        Controls severity of phase effects:

        - $\\tau \\in [0, 1]$ (normalized)
        - Higher $\\tau$: stronger derangement
        - Phase bounds: $x \\in [0, \\tau]$
        - Gadget output: $f(x) \\in [0, \\tau]$

        ---

        **See Also**: [Gadgets](gadgets.md), [Proofs](proofs.md)
        """).strip()

    def generate_hy_macros_documentation(self) -> str:
        """Generate Hy macros reference"""
        return textwrap.dedent("""
        # Hy Language Macros

        Complete reference for Hy macros provided by the Quantum Guitar skill.

        ## Core Macros

        ### defn* (Enhanced Definition)

        Enhanced function definition with automatic documentation and JAX JIT.

        ```hy
        (defn* function-name [args]
          {{:doc "Function documentation string"}}
          body)
        ```

        **Features**:
        - Automatic docstring storage
        - JAX JIT compilation flag
        - Metadata preservation

        ### phase-scoped (Phase Context)

        Execute code within phase context with automatic verification.

        ```hy
        (phase-scoped phase-var
          (do-something-in-phase))
        ```

        **Ensures**:
        - Phase timestamp ordering
        - Causality checking
        - Error handling with phase context

        ### verify (Lightweight Assertions)

        Assert with descriptive error messages.

        ```hy
        (verify assertion-expression
                "Error message if fails")
        ```

        ### with-proof (Proof Generation Context)

        Execute code and automatically generate proof artifacts.

        ```hy
        (with-proof :pyzx
          (create-gadget phase))
        ```

        **Generates**:
        - Proof timestamps
        - Context tracking
        - Artifact storage

        ### defmonadic (Monadic Operations)

        Define chainable, composable operations.

        ```hy
        (defmonadic operation-name [args]
          result)
        ```

        **Properties**:
        - Composable: f(g(x))
        - Chainable: (-> x f g h)
        - Type-preserving

        ### defoperad (Operad Structures)

        Define compositional structures with formal rules.

        ```hy
        (defoperad operad-name
          "description"
          (fn [a b] (combine a b)))
        ```

        ## JAX Macros

        ### with-jax (JAX Context)

        Enable JAX transformations (JIT, grad, vmap).

        ```hy
        (with-jax
          (setv f (jax.jit my-function))
          (setv grad-f (jax.grad f)))
        ```

        ### hy-jax-transform (Function Transformation)

        Transform Hy function to JAX-compiled versions.

        ```hy
        (setv transformed
          (hy-jax-transform my-fn 'jitted-fn))
        ```

        **Returns**:
        - `:original`: Original function
        - `:jitted`: JIT-compiled version
        - `:gradient`: Gradient function
        - `:transforms`: All transformations

        ## ZX-Calculus Macros

        ### hy-zx-proof (ZX Proof Definition)

        Define ZX-calculus proofs in Hy syntax.

        ```hy
        (hy-zx-proof proof-name
          (create-pyzx-proof "red"))
        ```

        ## Examples

        ### Example 1: Define Phase Gadget

        ```hy
        (defn* red-gadget [tau strength]
          {:doc "RED phase gadget: covariant forward rewrite"}
          (fn [x]
            (* x (+ 1.0 strength))))

        (defn* blue-gadget [tau strength]
          {:doc "BLUE phase gadget: contravariant backward rewrite"}
          (fn [x]
            (/ x (+ 1.0 strength))))
        ```

        ### Example 2: Phase Transition with Verification

        ```hy
        (defn* phase-transition [phase1 phase2 state]
          {:doc "Transition between phases with correctness check"}
          (phase-scoped phase2
            (do
              (verify (< (. phase1 timestamp) (. phase2 timestamp))
                      "Phase causality violated")
              (setv output1 (apply phase1 [state]))
              (setv output2 (apply phase2 [output1]))
              (verify (<= output2 (. phase2 tau))
                      "Phase bounds exceeded")
              output2)))
        ```

        ### Example 3: JAX-Compiled Derangement Measure

        ```hy
        (with-jax
          (defn* derangement-strength [config]
            {:doc "Measure derangement using JAX autodiff"}
            (fn [x]
              (jnp.abs (- (jnp.sin (* x jnp.pi)) x))))

          (setv grad-derangement (jax.grad derangement-strength)))
        ```

        ---

        **See Also**: [HyJAX Integration](hyjax.md), [Examples](examples.md)
        """).strip()

# ============================================================================
# PART 2: LLMs.txt Index Generator
# ============================================================================

class LLMsTextGenerator:
    """Generate LLMs.txt index for model discoverability"""

    def __init__(self, project_name: str, version: str = "1.0"):
        self.project_name = project_name
        self.version = version

    def generate(self) -> str:
        """Generate complete LLMs.txt"""
        return textwrap.dedent(f"""
        # {self.project_name} - Complete Documentation for LLMs
        ## Version {self.version}
        ## Generated: {datetime.now().isoformat()}

        ---

        ## EXECUTIVE SUMMARY

        This is a **persistent quantum computing world** implementing:

        1. **Formal Verification (Lean 4)**: Galois connection derangement theory
        2. **Hy Language Skill**: Complete source code + all macros + HyJAX
        3. **Proof Visualization**: PyZX (ZX-calculus), HyZX, Quizx (quantum circuits)
        4. **Persistent State**: World serialization and deep learning integration
        5. **Wiki & Documentation**: MkDocs structure for human exploration

        ---

        ## ARCHITECTURE OVERVIEW

        ```
        QuantumGuitarWorld
        ├── Lean 4 Layer (Formal Verification)
        │   ├── GaloisDerangement.lean      (400 LOC)
        │   └── Theorems: phase-scoped correctness, derangement properties
        │
        ├── Hy Language Layer (Skills & Computation)
        │   ├── hy_skill_loader.hy          (700 LOC)
        │   ├── Core Macros: defn*, phase-scoped, verify, with-proof
        │   ├── JAX Integration: hy-jax-transform, with-jax
        │   ├── ZX Integration: hy-zx-proof, defoperad
        │   └── World Management: create-world, add-phase-to-world, add-gadget-to-world
        │
        ├── Python Proof Systems (800 LOC)
        │   ├── PyZX Proofs: RED/BLUE/GREEN gadget proofs
        │   ├── HyZX Proofs: Hy + ZX-calculus fusion
        │   └── Quizx Proofs: OpenQASM quantum circuits
        │
        ├── Persistent World State
        │   ├── Phases (3 types): RED, BLUE, GREEN
        │   ├── Gadgets (verified rewrite rules)
        │   ├── Proofs (3 proof systems)
        │   ├── Traces (audit trail)
        │   └── Critical Phases (Galois derangement maxima)
        │
        └── Deep Wiki & Documentation
            ├── MkDocs structure
            ├── Semantic index
            └── LLMs.txt (this file)
        ```

        ---

        ## QUANTUM GUITAR PHASES

        ### RED Phase (Polarity = +1, Covariant)

        **Mathematical Definition**:
        ```
        f(x) ≥ x  for all x ∈ [0, τ]
        f(x) = x(1 + strength)
        ```

        **Properties**:
        - Monotone: x ≤ y ⟹ f(x) ≤ f(y)
        - Amplification (ferromagnetic expansion)
        - Forward causality

        **Audio**: Rising frequencies, brighter timbre, circle of fifths progressions

        **Proof Systems**:
        - PyZX: X-spiders → Z-spider (amplification) → X-spiders
        - Quizx: Rotation gates (ry(+θ)), RED qubit controls GREEN
        - HyZX: Hy code with explicit amplification theorem

        **OpenQASM Example**:
        ```
        ry(π/2 * τ) q[0];  // RED qubit amplification
        cx q[0], q[2];       // RED controls GREEN
        ```

        ### BLUE Phase (Polarity = -1, Contravariant)

        **Mathematical Definition**:
        ```
        f(x) ≤ x  for all x ∈ [0, τ]
        f(x) = x / (1 + strength)
        ```

        **Properties**:
        - Monotone (inverted): x ≤ y ⟹ f(x) ≥ f(y)
        - Contraction (antiferromagnetic simplification)
        - Backward causality / resolution

        **Audio**: Falling frequencies, duller timbre, tritone clusters, dissonance

        **Proof Systems**:
        - PyZX: Z-spiders → X-spider (contraction) → Z-spiders (Hadamard color-change)
        - Quizx: Inverted rotation gates (ry(-θ)), BLUE qubit controls GREEN
        - HyZX: Hy code with explicit contravariance theorem

        **OpenQASM Example**:
        ```
        ry(-π/2 * τ) q[1];  // BLUE qubit contraction
        cx q[1], q[2];        // BLUE controls GREEN
        ```

        ### GREEN Phase (Polarity = 0, Neutral)

        **Mathematical Definition**:
        ```
        f(x) = x  for all x ∈ [0, τ]
        ```

        **Properties**:
        - Identity: f(f(x)) = f(x) = x
        - Equilibrium point (paramagnetic)
        - Transparent phase boundary

        **Audio**: Constant frequency (pedal point), sustained drone, beating patterns

        **Proof Systems**:
        - PyZX: Single H-box (identity), simple edges
        - Quizx: Identity gates (id), GREEN controls both RED and BLUE
        - HyZX: Hy code with trivial identity proof

        **OpenQASM Example**:
        ```
        id q[2];      // GREEN: identity
        cx q[2], q[0]; // GREEN controls RED
        cx q[2], q[1]; // GREEN controls BLUE
        ```

        ---

        ## HY LANGUAGE SKILL

        ### Embedded Components

        **1. Complete Hy Source Code**
        - Latest stable version (0.29.0)
        - All core modules: hy.core, hy.macros, hy.compiler, hy.reader
        - Standard library functions

        **2. Best-Practice Macros**
        - Threading: `[->  ->>]` (left/right arrow threading)
        - Error handling: `[try except finally]`
        - Functional: `[map filter reduce]`
        - Control: `[if when unless cond]`
        - Meta: `[quote unquote eval]`
        - Monadic: `[do* >>= chain]`

        **3. HyJAX Integration**
        - Function transformation to JAX-compiled versions
        - Automatic differentiation: `(jax.grad f)`
        - JIT compilation: `(jax.jit f)`
        - Vectorization: `(jax.vmap f)`
        - Parallelization: `(jax.pmap f)`

        **4. Quantum Guitar Macros**

        #### defn* (Enhanced Definition)
        ```hy
        (defn* my-function [args]
          {:doc "Documentation"}
          body)
        ```
        - Automatic docstring preservation
        - Metadata storage
        - JAX-compatible

        #### phase-scoped (Phase Context)
        ```hy
        (phase-scoped phase-var
          body)
        ```
        - Ensures phase causality
        - Automatic timestamp checking
        - Error context

        #### verify (Assertions)
        ```hy
        (verify condition "Error message")
        ```
        - Lightweight, descriptive
        - Phase-aware

        #### with-proof (Proof Generation)
        ```hy
        (with-proof :pyzx
          (create-gadget phase))
        ```
        - Automatic artifact generation
        - Context tracking

        #### defmonadic (Composable Operations)
        ```hy
        (defmonadic operation [args]
          result)
        ```
        - Chainable with `(-> x f g h)`
        - Monad-like composition

        #### defoperad (Formal Structures)
        ```hy
        (defoperad name structure
          (fn [a b] (combine a b)))
        ```
        - Composition rules with formal guarantees
        - Operadic structure preservation

        #### with-jax (Autodiff Context)
        ```hy
        (with-jax
          (setv f (jax.jit my-function))
          (setv grad-f (jax.grad f)))
        ```
        - JAX transformations in Hy context
        - Implicit imports

        #### hy-zx-proof (ZX Definitions)
        ```hy
        (hy-zx-proof proof-name
          body)
        ```
        - ZX-calculus proofs in Hy
        - Automatic diagram generation

        ---

        ## FORMAL PROOF SYSTEMS

        ### PyZX System

        **Language**: Python + ZX-calculus

        **Gadgets**:

        #### RED Gadget Proof
        - Input: X-spider (qubit 0)
        - Operation: Z-spider amplification (strength-dependent)
        - Output: X-spider with phase boundary
        - Edges: Hadamard (covariant flow)
        - Reduction: Full ZX simplification

        **Theorem**:
        ```
        ∀ x ∈ [0, τ]:
          f(x) = x(1 + strength) ≥ x
          Monotone: x ≤ y ⟹ f(x) ≤ f(y)
          Phase-respecting: f(x) ≤ τ
        ```

        #### BLUE Gadget Proof
        - Input: Z-spider (qubit 1, contravariant)
        - Operation: X-spider contraction (strength-dependent)
        - Output: Z-spider with Hadamard color-change
        - Edges: Hadamard (contravariant flow)
        - Reduction: Full ZX simplification

        **Theorem**:
        ```
        ∀ x ∈ [0, τ]:
          f(x) = x / (1 + strength) ≤ x
          Monotone-inverted: x ≤ y ⟹ f(x) ≥ f(y)
          Phase-respecting: f(x) ≤ τ
        ```

        #### GREEN Gadget Proof
        - Input: Identity H-box (qubit 2)
        - Operation: Transparent identity
        - Output: Identity H-box
        - Edges: Simple (no color change)
        - Reduction: Trivial (no reduction possible)

        **Theorem**:
        ```
        ∀ x ∈ [0, τ]:
          f(x) = x (identity)
          Idempotent: f(f(x)) = f(x)
          Phase-respecting: trivial
        ```

        ### HyZX System

        **Language**: Hy + ZX-calculus

        **Features**:
        - ZX diagrams expressed as Hy code
        - Graph operations as Hy forms
        - Reduction rules as Hy macros
        - Proof extraction to Hy functions

        **Example RED Proof in HyZX**:
        ```hy
        (hy-zx-proof red-amplify-proof
          (do
            (setv diagram (zx-graph))
            (setv input-v (diagram.add-vertex :x-input))
            (setv amp-spider (diagram.add-vertex :z-spider))
            (setv output-v (diagram.add-vertex :x-output))
            (diagram.add-edge input-v amp-spider :hadamard)
            (diagram.add-edge amp-spider output-v :hadamard)
            (setv reduced (zx-reduce diagram))
            (setv circuit (zx-extract-circuit reduced))
            {{:diagram diagram
              :reduced reduced
              :circuit circuit
              :verified True}}))
        ```

        ### Quizx System

        **Language**: OpenQASM 2.0 (Quantum Assembly)

        **Implementation**:

        #### RED Gadget Circuit
        ```
        OPENQASM 2.0;
        include "qelib1.inc";

        qreg q[3];    // RED, BLUE, GREEN qubits
        creg c[3];    // Classical bits

        // RED phase: f(x) ≥ x
        ry(π/2 * τ) q[0];    // RED qubit rotation
        cx q[0], q[2];         // RED controls GREEN

        measure q -> c;
        ```

        #### BLUE Gadget Circuit
        ```
        OPENQASM 2.0;
        include "qelib1.inc";

        qreg q[3];
        creg c[3];

        // BLUE phase: f(x) ≤ x
        ry(-π/2 * τ) q[1];   // BLUE qubit (inverted)
        cx q[1], q[2];         // BLUE controls GREEN

        measure q -> c;
        ```

        #### GREEN Gadget Circuit
        ```
        OPENQASM 2.0;
        include "qelib1.inc";

        qreg q[3];
        creg c[3];

        // GREEN phase: f(x) = x
        id q[2];       // Identity on GREEN
        cx q[2], q[0]; // GREEN controls RED
        cx q[2], q[1]; // GREEN controls BLUE

        measure q -> c;
        ```

        ---

        ## PERSISTENT WORLD STATE

        ### World Structure

        ```python
        QuantumGuitarWorld(
          id: str,                    # Unique world identifier
          phases: Dict[int, Phase],    # Phase registry
          gadgets: Dict[int, Gadget],  # Verified gadgets
          proofs: Dict[str, Proof],    # Formal proofs
          traces: List[Tuple],         # Audit trail
          critical_phases: Set[int],   # Galois derangement maxima
          metadata: Dict               # User data
        )
        ```

        ### Serialization (JSON)

        ```json
        {{
          "id": "quantum-guitar:1703131200.5",
          "metadata": {{
            "created_at": 1703131200.5,
            "name": "quantum-guitar-derangement"
          }},
          "phases": {{
            "1": {{"id": 1, "polarity": 1, "tau": 0.5, "timestamp": 1}},
            "2": {{"id": 2, "polarity": -1, "tau": 0.5, "timestamp": 2}},
            "3": {{"id": 3, "polarity": 0, "tau": 0.5, "timestamp": 3}}
          }},
          "gadgets": {{}},
          "proofs": {{}},
          "critical_phases": []
        }}
        ```

        ### Audit Trail

        Every operation is logged:
        ```
        [(timestamp, phase_id, event), ...]
        Examples:
        - (1703131200.5, 1, "phase-added")
        - (1703131200.6, 1, "gadget-added")
        - (1703131200.7, "pyzx-red", "proof-added")
        ```

        ---

        ## MATHEMATICAL FOUNDATIONS

        ### Galois Connections

        **Definition**: A Galois connection between posets (X, ≤) and (Y, ≤) is a pair
        of monotone functions L: X → Y and R: Y → X such that:

        ```
        ∀ x ∈ X, y ∈ Y:  x ≤ R(y) ⟺ L(x) ≤ y
        ```

        ### Galois Derangement

        **Definition**: A permutation π on phase space is a Galois derangement if:

        ```
        1. IsDerangement(π):  ∀ i, π(i) ≠ i  (no fixed points)
        2. DisruptsAdjunction(π, gc):
           ∃ x, y: x ≤ gc.R(π(y)) ∧ π(y) < gc.L(π(x))
        ```

        ### Phase-Scoped Correctness

        **Theorem** (Main Correctness Result):

        ```
        ∀ φ₁, φ₂ : Phase
        ∀ g₁ : RewriteGadget(φ₁), g₂ : RewriteGadget(φ₂)

        φ₁.timestamp < φ₂.timestamp ∧
        IsCorrectAtPhase(φ₁, g₁) ∧
        IsCorrectAtPhase(φ₂, g₂)
        ⟹
        ∀ x : ℚ, x ≤ φ₁.τ:
          g₂.rule(g₁.rule(x)) ≤ φ₂.τ

        (Gadget composition preserves phase bounds across causality boundary)
        ```

        ### Polarity Semantics

        **RED (+1)**: f(x) ≥ x (Covariant, Ferromagnetic)
        ```
        Monotone: x ≤ y ⟹ f(x) ≤ f(y)
        Expansion: ∀ x: f(x) ≥ x
        Composition: RED ∘ RED = RED (closed)
        Incompatible: RED ∘ BLUE = ⊥
        ```

        **BLUE (-1)**: f(x) ≤ x (Contravariant, Antiferromagnetic)
        ```
        Monotone-inverted: x ≤ y ⟹ f(x) ≥ f(y)
        Contraction: ∀ x: f(x) ≤ x
        Composition: BLUE ∘ BLUE = BLUE (closed)
        Incompatible: BLUE ∘ RED = ⊥
        ```

        **GREEN (0)**: f(x) = x (Neutral, Paramagnetic)
        ```
        Identity: f(x) = x
        Idempotent: f(f(x)) = f(x)
        Composition: * ∘ GREEN = *, GREEN ∘ * = * (transparent)
        ```

        ---

        ## INTEGRATION GUIDE FOR LLMs

        ### For Code Generation

        Use the following context when generating code:

        1. **Phase system**: Always include phase parameter in functions
        2. **Verification**: Use `verify` macro for assertions
        3. **JAX**: Wrap numerical code with `with-jax` for autodiff
        4. **Proofs**: Generate PyZX, HyZX, and Quizx proofs together
        5. **World state**: Use `add-gadget-to-world`, `add-proof-to-world`, etc.

        ### For Mathematical Reasoning

        1. **Galois connections**: Always check for adjunction property violations
        2. **Derangements**: Look for no fixed points
        3. **Phases**: Respect timestamp ordering (causality)
        4. **Composition**: Verify polarity compatibility before combining gadgets

        ### For Documentation

        1. Always include mathematical formulas with $$ delimiters
        2. Reference phase polarities: RED, BLUE, or GREEN
        3. Link to proof artifacts: PyZX diagrams, Quizx circuits
        4. Explain both mathematical and audio interpretations

        ---

        ## QUICK REFERENCE

        **Load World**: `(load-quantum-guitar-world)`
        **Create Phase**: `(create-phase id tau timestamp polarity)`
        **Create Gadget**: `(create-gadget phase rule properties)`
        **Generate Proofs**: `(create-all-proofs phase gadget)`
        **Serialize**: `(world->json world)`
        **Deserialize**: `(json->world json-str)`

        **Composition Check**: `(compose-gadgets-correctness g1 g2 test-points)`
        **Phase Transition**: `(verify-phase-transition scope state phase1 phase2)`

        **PyZX Reduce**: `(zx-reduce graph)`
        **HyZX Proof**: `(hy-zx-proof name body)`
        **Quizx Circuit**: `(create-quizx-proof phase gadget)`

        **JAX Transform**: `(hy-jax-transform function 'name)`
        **Compute Gradient**: `(jax.grad f)`
        **JIT Compile**: `(jax.jit f)`

        ---

        **Documentation Version**: {self.version}
        **Last Updated**: {datetime.now().isoformat()}
        **Project**: {self.project_name}
        """).strip()

# ============================================================================
# Execution
# ============================================================================

if __name__ == "__main__":
    # Generate wiki
    wiki = WikiGenerator("Quantum Guitar Galois Derangement World")
    wiki.add_page("index.md", "Home", wiki.generate_homepage())
    wiki.add_page("quantum_guitar/phases.md", "Phases", wiki.generate_phases_documentation())
    wiki.add_page("hy_skill/macros.md", "Macros", wiki.generate_hy_macros_documentation())

    print("=" * 80)
    print("WIKI GENERATION")
    print("=" * 80)
    print(wiki.generate_mkdocs_yml())

    # Generate LLMs.txt
    llms = LLMsTextGenerator("Quantum Guitar Galois Derangement World")
    llms_content = llms.generate()

    print("\n" + "=" * 80)
    print("LLMs.txt GENERATION")
    print("=" * 80)
    print(llms_content[:2000] + "\n... (truncated for display) ...\n")

    # Save to files
    Path("mkdocs.yml").write_text(wiki.generate_mkdocs_yml())
    Path("LLMs.txt").write_text(llms_content)
    print("\n✓ Files saved:")
    print("  - mkdocs.yml")
    print("  - LLMs.txt")
