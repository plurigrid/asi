---
name: cue-lang
description: 'CUE: Lattice-based configuration language with unification, constraint
  validation, and OpenAPI/JSON Schema generation'
source: cue-lang/cue (Go)
license: Apache-2.0
trit: 1
gf3_conserved: true
repo_divergence: LOW (DeepWiki accurate)
last_commit: 2025-12-21 (active)
metadata:
  interface_ports:
  - Related Skills
---
# CUE (+1)

> Configuration, data validation, and code generation via lattice unification.

**Trit**: +1 (PLUS - generative type lattice)
**Language**: Go
**Branch**: `master`

## Core Insight: Values ARE Types

```cue
// In CUE, every value is also a type constraint
name: string        // type constraint
name: "alice"       // concrete value IS a subtype

// Unification: greatest lower bound
a: {x: int, y: string}
b: {x: 1, z: bool}
c: a & b  // → {x: 1, y: string, z: bool}
```

## Lattice Type System

```
           ⊤ (any)
          / | \
       int str bool
        |   |   |
        1  "a" true
          \ | /
           ⊥ (error)

Unification = Greatest Lower Bound (GLB)
int & 1 → 1
int & string → ⊥ (error)
```

## Key Features

| Feature | CUE | JSON Schema | TypeScript |
|---------|-----|-------------|------------|
| Values = Types | ✓ | ✗ | ✗ |
| Unification | ✓ | ✗ | ✗ |
| Constraints | ✓ | Partial | Partial |
| Code gen | ✓ | ✗ | ✗ |
| Turing-complete | ✗ | ✗ | ✓ |

**CUE is intentionally NOT Turing-complete** - guarantees termination.

## Syntax Essentials

```cue
package myconfig

import "list"

// Definitions (templates)
#Person: {
    name:  string
    age:   int & >=0 & <=150
    email: =~"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$"
}

// Concrete values
alice: #Person & {
    name:  "Alice"
    age:   30
    email: "alice@example.com"
}

// List comprehensions
numbers: [1, 2, 3, 4, 5]
doubled: [for x in numbers {x * 2}]

// Disjunction (sum types)
Status: "pending" | "active" | "complete"
```

## Schema Integration

```bash
# CUE → JSON Schema
cue export --out jsonschema schema.cue

# CUE → OpenAPI
cue export --out openapi api.cue

# Go types → CUE
cue get go ./pkg/...

# Validate YAML/JSON against CUE
cue vet data.yaml schema.cue
```

## Comparison with Nickel

| Aspect | CUE | Nickel |
|--------|-----|--------|
| Type system | Lattice unification | Gradual typing + contracts |
| Evaluation | Lazy, no side effects | Lazy, pure |
| Turing-complete | No (terminates) | Yes |
| Error messages | Structural | Blame tracking |
| Primary use | K8s/Cloud config | General config |

## Sexp Bridge

```cue
// CUE can export to various formats
output: json.Marshal(config)   // → JSON
output: yaml.Marshal(config)   // → YAML

// For sexp, use external tool:
// cue export config.cue | json2sexp
```

Integration with lispsyntax-acset:
```julia
# Julia: parse CUE output, convert to sexp
using JSON3, LispSyntax

cue_json = read(`cue export config.cue`, String)
data = JSON3.read(cue_json)
sexp = json_to_sexp(data)  # Custom bridge
```

## GF(3) Config Triad

```
CUE (+1)    + Nickel (0)  + Hof (-1)    = 0 ✓
generative   ergodic       extractive
schemas      contracts     code gen
```

## Sexp Neighborhood

| Skill | Trit | Bridge to CUE |
|-------|------|---------------|
| **hof** | -1 | Consumes CUE, generates code |
| **nickel** | 0 | Alternative with contracts |
| **lispsyntax-acset** | 0 | CUE → JSON → sexp → ACSet |
| **geb** | +1 | Both use algebraic types |
| **gay-mcp** | +1 | Color CUE schema elements |

## Usage

```bash
# Install
go install cuelang.org/go/cmd/cue@latest

# Evaluate
cue eval config.cue

# Export to JSON
cue export config.cue

# Validate
cue vet data.yaml schema.cue

# Format
cue fmt *.cue

# Get Go types
cue get go ./...
```

## Kubernetes Example

```cue
package k8s

import "k8s.io/api/apps/v1"

#Deployment: v1.#Deployment & {
    apiVersion: "apps/v1"
    kind:       "Deployment"
    metadata: {
        name:      string
        namespace: string | *"default"
    }
    spec: {
        replicas: int & >=1 & <=100 | *3
        selector: matchLabels: app: metadata.name
        template: {
            metadata: labels: app: metadata.name
            spec: containers: [...#Container]
        }
    }
}

#Container: {
    name:  string
    image: string
    ports: [...{containerPort: int}]
}
```

## CLI Commands

```bash
# Core commands
cue eval      # Evaluate and print
cue export    # Export to JSON/YAML/etc
cue vet       # Validate data
cue def       # Print definitions
cue fmt       # Format files
cue get       # Import from Go/Proto
cue mod       # Module management
cue trim      # Remove redundant values
```

---

## End-of-Skill Interface

## Related Skills

| Skill | Trit | Relationship |
|-------|------|--------------|
| hof | -1 | CUE consumer for codegen |
| nickel | 0 | Alternative approach |
| geb | +1 | Algebraic type sibling |
| acsets | 0 | Schema → ACSet bridge |

---

**Trit**: +1 (PLUS - generative lattice)
**Key Property**: Unification-based config with guaranteed termination
**Philosophy**: Values ARE types, constraints compose via GLB


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
