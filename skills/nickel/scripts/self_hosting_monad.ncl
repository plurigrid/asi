# Self-Hosting 2-Categorical Monad for Nickel
# GF(3) Trit: 0 (ERGODIC)
#
# A 2-monad where:
#   0-cells = Contracts (types)
#   1-cells = Functions (transformations)
#   2-cells = Merge operations (natural transformations)

# ═══════════════════════════════════════════════════════════════════════════
# LEVEL 0: Core 2-Monad Structure
# ═══════════════════════════════════════════════════════════════════════════

# Monadic wrapper: value + metadata + contract stack
let Wrapped = {
  value 
    | doc "The wrapped value",
  
  meta
    | { _ : _ }
    | default = {}
    | doc "Metadata accumulated through transformations",
  
  contracts
    | Array String
    | default = []
    | doc "Contract names applied (for tracing)"
}

# Unit: inject into monad (η : Id → T)
let unit = fun x => {
  value = x,
  meta = { created_at = "now", level = 0 },
  contracts = []
}

# Bind: sequence monadic computations (Kleisli extension)
let bind = fun ma f =>
  let mb = f ma.value in
  mb & {
    meta = ma.meta & mb.meta & { level = ma.meta.level + 1 },
    contracts = std.array.concat ma.contracts mb.contracts
  }

# Multiplication: flatten T(T(a)) → T(a) (μ : T² → T)
let mult = fun tta =>
  tta.value & {
    meta = tta.meta & tta.value.meta,
    contracts = std.array.concat tta.contracts tta.value.contracts
  }

# ═══════════════════════════════════════════════════════════════════════════
# LEVEL 1: 2-Cells as Contract Transformations
# ═══════════════════════════════════════════════════════════════════════════

# A 2-cell between 1-cells f, g : A → B
let TwoCell = {
  source
    | String
    | doc "Source 1-cell name",
  
  target  
    | String
    | doc "Target 1-cell name",
  
  witness
    | doc "Proof/transformation between source and target"
}

# Horizontal composition of 2-cells (⊗)
let horiz_comp = fun alpha beta => {
  source = "%{alpha.source} ; %{beta.source}",
  target = "%{alpha.target} ; %{beta.target}",
  witness = { left = alpha.witness, right = beta.witness }
}

# Vertical composition of 2-cells (•)
let vert_comp = fun alpha beta => {
  source = alpha.source,
  target = beta.target,
  witness = { bottom = alpha.witness, top = beta.witness }
}

# ═══════════════════════════════════════════════════════════════════════════
# LEVEL 2: Self-Hosting (Metacircular) Patterns
# ═══════════════════════════════════════════════════════════════════════════

# AST node types (from tree-sitter-nickel)
let AstNode = [|
  'atom, 'bool, 'num_literal, 'str_chunks,
  'ident, 'fun, 'applicative, 'let_expr,
  'if_then_else, 'record_operand, 'annot,
  'infix_expr, 'match_expr, 'import
|]

# Environment as record
let Env = { _ : _ }

# Minimal self-interpreter sketch
let self_eval = {
  eval_atom = fun node env =>
    if node.type == 'bool then node.value
    else if node.type == 'num_literal then node.value
    else if node.type == 'ident then std.record.get node.name env
    else node,
  
  eval_fun = fun node env =>
    { type = 'closure, param = node.param, body = node.body, env = env },
  
  eval_app = fun node env =>
    let fn = self_eval.eval node.fn env in
    let arg = self_eval.eval node.arg env in
    if fn.type == 'closure 
    then self_eval.eval fn.body (fn.env & { "%{fn.param}" = arg })
    else { error = "not a function" },
  
  # Dispatcher
  eval = fun node env =>
    if std.array.elem node.type ['bool, 'num_literal, 'ident]
    then self_eval.eval_atom node env
    else if node.type == 'fun
    then self_eval.eval_fun node env
    else if node.type == 'applicative
    then self_eval.eval_app node env
    else { unhandled = node.type }
}

# ═══════════════════════════════════════════════════════════════════════════
# LEVEL 3: CatColab Double Theory Bridge
# ═══════════════════════════════════════════════════════════════════════════

# Double theory as Nickel contract
let DoubleTheory = {
  name
    | String
    | doc "Theory name",
  
  ob_generators
    | Array String
    | doc "0-cell generators",
  
  mor_generators
    | Array { name: String, source: String, target: String }
    | doc "1-cell generators",
  
  equations
    | Array { lhs: String, rhs: String }
    | default = []
    | doc "Path equations"
}

# Stock-Flow theory (Topos Institute epidemiology)
let ThStockFlow : DoubleTheory = {
  name = "StockFlow",
  ob_generators = ["Stock"],
  mor_generators = [
    { name = "Flow", source = "Stock", target = "Stock" },
    { name = "Link", source = "Stock", target = "Stock" }
  ],
  equations = []
}

# Category theory basics
let ThCategory : DoubleTheory = {
  name = "Category",
  ob_generators = ["Ob"],
  mor_generators = [
    { name = "Hom", source = "Ob", target = "Ob" }
  ],
  equations = [
    { lhs = "id ; f", rhs = "f" },
    { lhs = "f ; id", rhs = "f" },
    { lhs = "(f ; g) ; h", rhs = "f ; (g ; h)" }
  ]
}

# ═══════════════════════════════════════════════════════════════════════════
# CURRICULUM: 2-Tutorial Paths
# ═══════════════════════════════════════════════════════════════════════════

let Curriculum = {
  # Path A: WITH skills (load sicp, topos-catcolab, etc.)
  with_skills = [
    { id = 1, skill = "sicp", topic = "Metacircular evaluator" },
    { id = 2, skill = "topos-catcolab", topic = "Double theories" },
    { id = 3, skill = "nickel", topic = "Gradual contracts" },
    { id = 4, skill = "discopy", topic = "String diagrams" },
    { id = 5, skill = "open-games", topic = "Game semantics" },
    { id = 6, skill = "kan-extensions", topic = "Universal properties" },
    { id = 7, skill = "dialectica", topic = "Dialectica interpretation" }
  ],
  
  # Path B: WITHOUT skills (first-principles Nickel)
  without_skills = [
    { id = 1, file = "01_lambda.ncl", topic = "Lambda calculus" },
    { id = 2, file = "02_contracts.ncl", topic = "Type contracts" },
    { id = 3, file = "03_merge.ncl", topic = "Record merging as 2-cells" },
    { id = 4, file = "04_lazy.ncl", topic = "Lazy evaluation" },
    { id = 5, file = "05_import.ncl", topic = "Module system" },
    { id = 6, file = "06_recursion.ncl", topic = "Fixed points" },
    { id = 7, file = "07_bootstrap.ncl", topic = "Self-hosting" }
  ]
}

# ═══════════════════════════════════════════════════════════════════════════
# EXPORTS
# ═══════════════════════════════════════════════════════════════════════════

{
  # 2-Monad operations
  Wrapped = Wrapped,
  unit = unit,
  bind = bind,
  mult = mult,
  
  # 2-Cells
  TwoCell = TwoCell,
  horiz_comp = horiz_comp,
  vert_comp = vert_comp,
  
  # Self-hosting
  AstNode = AstNode,
  self_eval = self_eval,
  
  # CatColab bridge
  DoubleTheory = DoubleTheory,
  ThStockFlow = ThStockFlow,
  ThCategory = ThCategory,
  
  # Curriculum
  Curriculum = Curriculum
}
