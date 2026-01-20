{- 
  Skill.dhall - Type-safe, total skill configuration
  
  Dhall is a programmable configuration language that guarantees:
  - Totality (no infinite loops, always terminates)
  - Type safety (catch errors at config-generation time)
  - Hermetic (no side effects, reproducible)
  
  This defines the core skill schema with GF(3) trit assignments.
-}

-- GF(3) trit type: the fundamental classification
let Trit = < Plus | Ergodic | Minus >

-- Convert trit to integer for balance checking
let tritToInt : Trit → Integer = λ(t : Trit) →
  merge { Plus = +1, Ergodic = +0, Minus = -1 } t

-- A Skill is the atomic unit of capability
let Skill = {
  name : Text,
  description : Text,
  trit : Trit,
  category : Text,
  dependencies : List Text,
  bridges : List Text,
  version : Text,
  examples : List Text
}

-- Default skill values
let defaultSkill : Skill = {
  name = "",
  description = "",
  trit = Trit.Ergodic,
  category = "uncategorized",
  dependencies = [] : List Text,
  bridges = [] : List Text,
  version = "1.0.0",
  examples = [] : List Text
}

-- Skill constructors by trit type
let plusSkill : Text → Text → Text → Skill = λ(name : Text) → λ(desc : Text) → λ(cat : Text) →
  defaultSkill // { name = name, description = desc, trit = Trit.Plus, category = cat }

let ergodicSkill : Text → Text → Text → Skill = λ(name : Text) → λ(desc : Text) → λ(cat : Text) →
  defaultSkill // { name = name, description = desc, trit = Trit.Ergodic, category = cat }

let minusSkill : Text → Text → Text → Skill = λ(name : Text) → λ(desc : Text) → λ(cat : Text) →
  defaultSkill // { name = name, description = desc, trit = Trit.Minus, category = cat }

-- Polynomial interface for skills (Spivak semantics)
let PolyInterface = {
  positions : List Text,    -- Observation types
  directions : List Text    -- Action types
}

-- Extended skill with polynomial semantics
let PolySkill = {
  skill : Skill,
  interface : PolyInterface
}

-- The UNWORLD federation agents
let causality : Skill = plusSkill "causality" "Generative exploration agent" "federation"
let twoMonad : Skill = ergodicSkill "2-monad" "World coordination agent" "federation"  
let amp : Skill = minusSkill "amp" "Verification and constraint agent" "federation"

-- Modelica skill (acausal coordinator)
let modelica : Skill = ergodicSkill "modelica" 
  "Acausal equation-based modeling with connector semantics as lenses" 
  "simulation"

-- Sheaf cohomology skill (verification)
let sheafCohomology : Skill = minusSkill "sheaf-cohomology"
  "Čech complex computation for local-to-global consistency"
  "mathematics"

-- Polynomial operads skill (generation)
let polyOperads : Skill = plusSkill "asi-polynomial-operads"
  "Operad composition for skill wiring diagrams"
  "mathematics"

-- Temporal coalgebra skill (coordination)
let temporalCoalgebra : Skill = ergodicSkill "temporal-coalgebra"
  "Coalgebraic state machine semantics for agents"
  "mathematics"

-- Export all types and constructors
in {
  -- Types
  Trit = Trit,
  Skill = Skill,
  PolyInterface = PolyInterface,
  PolySkill = PolySkill,
  
  -- Functions
  tritToInt = tritToInt,
  defaultSkill = defaultSkill,
  plusSkill = plusSkill,
  ergodicSkill = ergodicSkill,
  minusSkill = minusSkill,
  
  -- Federation agents
  causality = causality,
  twoMonad = twoMonad,
  amp = amp,
  
  -- Core skills
  modelica = modelica,
  sheafCohomology = sheafCohomology,
  polyOperads = polyOperads,
  temporalCoalgebra = temporalCoalgebra
}
