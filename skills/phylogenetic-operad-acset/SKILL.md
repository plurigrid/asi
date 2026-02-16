# Phylogenetic Operad ACSet Skill

> **Trit**: 0 (ERGODIC) - Mediates between Com (commutative) and [0,∞) (metric)

Baez-Otter phylogenetic operad Phyl = Com + [0,∞) as ACSet schema, with mathpix-gem extraction and ∞-operad dendroidal integration.

## Core Insight: Phyl = Com + [0,∞)

From Baez & Otter (2017):

```
Phyl = coproduct of:
  • Com  - operad for commutative semigroups (tree topology)
  • [0,∞) - operad with unary ops = nonnegative reals (edge lengths)
  
Composition: edge length addition
```

**Key Theorem**: `Phyl(n) ≅ T_n × [0,∞)^{n+1}` where T_n = BHV treespace

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Phylogenetic Operad ACSet                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ┌──────────────┐    ┌──────────────┐    ┌──────────────┐              │
│   │     Com      │    │    Phyl      │    │   [0,∞)      │              │
│   │  (topology)  │───▶│  (coproduct) │◀───│  (metrics)   │              │
│   │   Trit=-1    │    │   Trit=0     │    │   Trit=+1    │              │
│   └──────────────┘    └──────────────┘    └──────────────┘              │
│          │                   │                   │                       │
│          └───────────────────┼───────────────────┘                       │
│                              ▼                                           │
│                    ┌──────────────┐                                      │
│                    │ ∞-Operads    │                                      │
│                    │ Dendroidal   │                                      │
│                    │   Ω-sets     │                                      │
│                    └──────────────┘                                      │
│                              │                                           │
│                              ▼                                           │
│                    ┌──────────────┐                                      │
│                    │   ACSet      │                                      │
│                    │  SchPhyl     │                                      │
│                    └──────────────┘                                      │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## ACSet Schema for Phyl

```julia
using Catlab, ACSets

# Phyl operad as ACSet schema
@present SchPhyl(FreeSchema) begin
    # Objects (tree structure)
    Node::Ob           # Internal nodes
    Leaf::Ob           # External leaves (taxa)
    Edge::Ob           # Edges with lengths
    Tree::Ob           # Complete phylogenetic tree
    
    # Morphisms (tree topology from Com)
    parent::Hom(Node, Node)           # Parent relation
    leaf_parent::Hom(Leaf, Node)      # Leaf attachment
    edge_source::Hom(Edge, Node)      # Edge endpoints
    edge_target::Hom(Edge, Node)
    root_of::Hom(Tree, Node)          # Tree root
    
    # Attribute types
    Length::AttrType   # [0,∞) edge lengths
    Taxa::AttrType     # Taxon labels
    Weight::AttrType   # Branch support
    
    # Attributes (metrics from [0,∞))
    edge_length::Attr(Edge, Length)   # t ∈ [0,∞)
    taxon_name::Attr(Leaf, Taxa)
    branch_support::Attr(Edge, Weight)
    
    # Operadic composition: grafting
    GraftOp::Ob
    graft_tree::Hom(GraftOp, Tree)    # Tree being grafted
    graft_at::Hom(GraftOp, Leaf)      # Leaf replaced by subtree
    graft_length::Attr(GraftOp, Length)  # Added edge length
end

@acset_type PhylACSet(SchPhyl, index=[:parent, :edge_source, :edge_target])
```

## Markov Coalgebras

Baez-Otter show Markov models give **coalgebras** of Phyl:

```julia
# Markov process on finite state space S
struct MarkovCoalgebra
    states::Vector{Symbol}       # Finite set S
    transition::Matrix{Float64}  # Q: S × S → ℝ (rate matrix)
    equilibrium::Vector{Float64} # π: stationary distribution
end

# Coalgebra structure: Phyl-coalgebra
function phyl_coalgebra(mc::MarkovCoalgebra, tree::PhylACSet)
    """
    For each edge e with length t:
      P(t) = exp(Q·t)  (transition probability matrix)
    
    Composition = matrix multiplication
    """
    for e in parts(tree, :Edge)
        t = tree[e, :edge_length]
        P_t = exp(mc.transition * t)
        # Apply P_t along edge e
    end
end

# Equilibrium extension: Phyl → Com + [0,∞]
function extend_to_infinity(mc::MarkovCoalgebra)
    """
    As t → ∞: P(t) → π ⊗ 1  (equilibrium)
    This gives coalgebra of Com + [0,∞] (with ∞ added)
    """
    return mc.equilibrium * ones(length(mc.states))'
end
```

## BHV Treespace T_n

The **Billera-Holmes-Vogtmann** treespace:

```julia
struct BHVTreespace
    n::Int              # Number of taxa
    trees::Vector{PhylACSet}
    
    # Geodesic distance in treespace
    function geodesic(t1::PhylACSet, t2::PhylACSet)
        # Owen-Provan polynomial-time algorithm
        # or GTP (Geodesic Tree Path)
    end
end

# Homeomorphism: Phyl(n) ≅ T_n × [0,∞)^{n+1}
function phyl_to_bhv(op::PhylACSet)
    topology = forget_lengths(op)  # T_n component
    lengths = extract_lengths(op)  # [0,∞)^{n+1} component
    return (topology, lengths)
end
```

## Mathpix-gem Integration

Extract phylogenetic trees from papers:

```ruby
# mathpix_phylo_extractor.rb
require 'mathpix'

module MathpixPhylo
  TREE_PATTERNS = {
    newick: /\([^)]*\([^)]*\)[^)]*\);/,           # Newick format
    latex_tree: /\\Tree\s*\[/,                     # qtree
    tikz_tree: /\\node.*child\s*\{/,              # TikZ trees
    forest_tree: /\\begin\{forest\}/               # forest package
  }
  
  class PhyloExtractor
    def extract_from_pdf(pdf_path)
      result = Mathpix::Client.convert_document(pdf_path)
      
      trees = []
      result.pages.each do |page|
        TREE_PATTERNS.each do |format, pattern|
          matches = page.latex.scan(pattern)
          matches.each do |match|
            trees << parse_tree(match, format)
          end
        end
      end
      
      trees
    end
    
    def parse_tree(latex, format)
      case format
      when :newick
        newick_to_acset(latex)
      when :latex_tree, :tikz_tree, :forest_tree
        latex_tree_to_acset(latex)
      end
    end
    
    def newick_to_acset(newick_str)
      # Parse Newick → PhylACSet
      tree = PhylACSet()
      # ... parsing logic
      tree
    end
  end
end
```

## Dendroidal ∞-Operad Connection

Link to infinity-operads skill:

```julia
# Phyl as dendroidal set
struct DendroidalPhyl
    """
    Phyl embeds into dSet (dendroidal sets) via:
      N_d(Phyl)(T) = Hom_Operad(Ω(T), Phyl)
    
    Objects of Ω: finite rooted trees
    Morphisms: face/degeneracy maps
    """
end

# Dendroidal nerve of Phyl
function dendroidal_nerve(phyl::PhylACSet)
    # For each tree shape T in Ω:
    #   N_d(Phyl)(T) = ways to label T with Phyl operations
    
    # Face maps: operadic composition
    # Degeneracy maps: identity insertion
end

# Boardman-Vogt construction
function boardman_vogt(O)
    """
    Baez-Otter Theorem: For any operad O,
      W(O) ⊂ O + [0,∞]
    
    where W(O) is the Boardman-Vogt resolution
    """
    return coproduct(O, interval_operad(0, Inf))
end
```

## GF(3) Conservation

```
# Phyl Triads

# Core decomposition
com-operad (-1) ⊗ phylogenetic-operad-acset (0) ⊗ metric-operad (+1) = 0 ✓

# ∞-operad integration  
segal-types (-1) ⊗ phylogenetic-operad-acset (0) ⊗ rezk-types (+1) = 0 ✓

# Markov coalgebra
temporal-coalgebra (-1) ⊗ phylogenetic-operad-acset (0) ⊗ markov-game-acset (+1) = 0 ✓

# ACSet foundation
acsets-relational-thinking (-1) ⊗ phylogenetic-operad-acset (0) ⊗ specter-acset (+1) = 0 ✓

# Mathpix extraction
sheaf-cohomology (-1) ⊗ phylogenetic-operad-acset (0) ⊗ mathpix-ocr (+1) = 0 ✓
```

## ACSet Taxonomy Position

```
                    ┌─────────────────────────────┐
                    │   acset-taxonomy (meta)      │
                    └─────────────────┬───────────┘
                                      │
          ┌───────────────────────────┼───────────────────────────┐
          │                           │                           │
   ┌──────▼──────┐            ┌───────▼───────┐           ┌───────▼───────┐
   │  EXPLICIT   │            │  DOMAIN-      │           │ SEMANTICALLY  │
   │  ACSET      │            │  SPECIFIC     │           │ SIMILAR       │
   └─────────────┘            └───────┬───────┘           └───────────────┘
                                      │
                      ┌───────────────┼───────────────┐
                      │               │               │
               ┌──────▼──────┐ ┌──────▼──────┐ ┌──────▼──────┐
               │ calendar-   │ │phylogenetic-│ │ protocol-   │
               │ acset       │ │operad-acset │ │ acset       │
               └─────────────┘ └─────────────┘ └─────────────┘
                                    │
                           ┌────────┴────────┐
                           │                 │
                    ┌──────▼──────┐   ┌──────▼──────┐
                    │ infinity-   │   │ mathpix-    │
                    │ operads     │   │ ocr         │
                    └─────────────┘   └─────────────┘
```

## Usage Examples

### Extract Phylogenetic Tree from Paper

```bash
# Via mathpix-gem MCP
claude mcp mathpix convert_document --path baez_phylo.pdf --extract-trees

# Direct extraction
bundle exec ruby -r mathpix_phylo -e "
  extractor = MathpixPhylo::PhyloExtractor.new
  trees = extractor.extract_from_pdf('paper.pdf')
  trees.each { |t| puts t.to_newick }
"
```

### Create PhylACSet from Newick

```julia
using PhylogeneticOperadACSet

# Parse Newick string
tree = newick_to_phyl("((A:0.1,B:0.2):0.3,(C:0.4,D:0.5):0.6):0.7;")

# Operadic composition: graft tree2 onto tree1 at leaf "A"
tree2 = newick_to_phyl("(E:0.8,F:0.9):1.0;")
grafted = graft!(tree, tree2, at_leaf=:A, add_length=0.05)

# Verify GF(3) conservation
@assert gf3_balanced(grafted)
```

### Compute Geodesic in BHV Treespace

```julia
# Two trees on same taxa
t1 = newick_to_phyl("((A,B),(C,D));")
t2 = newick_to_phyl("((A,C),(B,D));")

# Geodesic distance
d = bhv_geodesic(t1, t2)

# Interpolate along geodesic
path = geodesic_path(t1, t2, steps=10)
```

### Dendroidal Nerve

```julia
# Compute dendroidal nerve of Phyl
nerve = dendroidal_nerve(phyl_operad)

# Check Segal condition
@assert segal_condition(nerve)

# Apply to ∞-operad algebra
algebra = phyl_algebra(target_category)
```

## Theoretical Background

### Coproduct of Operads (Baez-Otter)

For operads O and P, their coproduct O + P has:
- Operations: labelled trees with vertices from O ∪ P
- Composition: grafting trees at leaves

For Phyl = Com + [0,∞):
- Com operations: symmetric trees (any arity)
- [0,∞) operations: unary with length t ∈ [0,∞)
- Result: metric trees with commutative branching

### Coalgebra Perspective

A **Phyl-coalgebra** is:
- Set X (states)  
- For each n-ary operation in Phyl(n): map X → X^n
- Naturality: respects operadic composition

**Markov models** give canonical examples:
- X = finite set of nucleotides/amino acids
- Phyl(n) action via transition matrices P(t)

## References

- Baez, J.C. & Otter, N. (2017). [Operads and Phylogenetic Trees](https://arxiv.org/abs/1512.03337). arXiv:1512.03337
- Billera, L.J., Holmes, S.P. & Vogtmann, K. (2001). Geometry of the space of phylogenetic trees. *Advances in Applied Mathematics* 27, 733-767.
- Boardman, J.M. & Vogt, R.M. (1973). Homotopy Invariant Algebraic Structures on Topological Spaces. LNM 347.
- Owen, M. & Provan, J.S. (2011). A fast algorithm for computing geodesic distances in tree space. *IEEE/ACM Trans. Computational Biology and Bioinformatics* 8(1), 2-13.

## See Also

- [infinity-operads](file:///Users/bob/.claude/skills/infinity-operads/SKILL.md) - Dendroidal sets, Segal conditions
- [mathpix-ocr](file:///Users/bob/.claude/skills/mathpix-ocr/SKILL.md) - LaTeX extraction with balanced ternary
- [acset-taxonomy](file:///Users/bob/.claude/skills/acset-taxonomy/SKILL.md) - ACSet skill morphisms
- [temporal-coalgebra](file:///Users/bob/.claude/skills/temporal-coalgebra/SKILL.md) - Coalgebraic observation
- [markov-game-acset](file:///Users/bob/.claude/skills/markov-game-acset/SKILL.md) - State-dependent strategies


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
