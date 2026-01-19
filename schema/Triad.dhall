{-
  Triad.dhall - GF(3)-balanced skill composition
  
  A Triad is three skills whose trits sum to 0 (mod 3).
  This enforces conservation at compile-time using Dhall's type system.
  
  Valid triad patterns:
    (+1, 0, -1)   = plus, ergodic, minus
    (+1, +1, +1)  = 3 ≡ 0 (mod 3)
    (-1, -1, -1)  = -3 ≡ 0 (mod 3)
    (0, 0, 0)     = ergodic, ergodic, ergodic
-}

let Skill = ./Skill.dhall

-- A Triad is a balanced triple of skills
let Triad = {
  s1 : Skill.Skill,
  s2 : Skill.Skill,
  s3 : Skill.Skill,
  name : Text,
  description : Text
}

-- Calculate the sum of trits
let triadSum : Triad → Integer = λ(t : Triad) →
  Skill.tritToInt t.s1.trit + Skill.tritToInt t.s2.trit + Skill.tritToInt t.s3.trit

-- Check if a triad is balanced (sum ≡ 0 mod 3)
let isBalanced : Triad → Bool = λ(t : Triad) →
  let sum = triadSum t
  let absSum = if Integer/isNegative sum then Integer/negate sum else sum
  in Natural/isZero (Integer/clamp absSum % 3)

-- Enforce balance at compile time by requiring proof
-- This uses Dhall's assert to reject unbalanced triads
let assertBalanced : Triad → Triad = λ(t : Triad) →
  let _ = assert : isBalanced t === True
  in t

-- Create a triad with automatic balance checking
let mkTriad : Skill.Skill → Skill.Skill → Skill.Skill → Text → Text → Triad =
  λ(s1 : Skill.Skill) → λ(s2 : Skill.Skill) → λ(s3 : Skill.Skill) → 
  λ(name : Text) → λ(desc : Text) →
    assertBalanced { s1 = s1, s2 = s2, s3 = s3, name = name, description = desc }

-- Standard triad patterns
let Pattern = < PlusErgodicMinus | AllPlus | AllMinus | AllErgodic >

-- Create skills matching a pattern
let patternToTrits : Pattern → { t1 : Skill.Trit, t2 : Skill.Trit, t3 : Skill.Trit } =
  λ(p : Pattern) → merge {
    PlusErgodicMinus = { t1 = Skill.Trit.Plus, t2 = Skill.Trit.Ergodic, t3 = Skill.Trit.Minus },
    AllPlus = { t1 = Skill.Trit.Plus, t2 = Skill.Trit.Plus, t3 = Skill.Trit.Plus },
    AllMinus = { t1 = Skill.Trit.Minus, t2 = Skill.Trit.Minus, t3 = Skill.Trit.Minus },
    AllErgodic = { t1 = Skill.Trit.Ergodic, t2 = Skill.Trit.Ergodic, t3 = Skill.Trit.Ergodic }
  } p

-- The UNWORLD Federation triad
let unworldFederation : Triad = mkTriad 
  Skill.causality 
  Skill.twoMonad 
  Skill.amp
  "unworld-federation"
  "The three UNWORLD agents: causality (+1), 2-monad (0), amp (-1)"

-- Mathematical verification triad
let mathVerification : Triad = mkTriad
  Skill.polyOperads       -- +1: generates compositions
  Skill.temporalCoalgebra -- 0: coordinates state
  Skill.sheafCohomology   -- -1: verifies consistency
  "math-verification"
  "Polynomial operads + temporal coalgebra + sheaf cohomology"

-- Modelica simulation triad
let modelicaSimulation : Triad = 
  let langevin = Skill.plusSkill "langevin-dynamics" "Stochastic dynamics" "physics"
  let fokkerPlanck = Skill.minusSkill "fokker-planck" "Probability verification" "physics"
  in mkTriad langevin Skill.modelica fokkerPlanck
    "modelica-simulation"
    "Langevin dynamics (+1) + Modelica (0) + Fokker-Planck (-1)"

-- Quad: A balanced quad is two triads sharing an edge
let Quad = {
  triad1 : Triad,
  triad2 : Triad,
  sharedSkill : Skill.Skill
}

-- Create a quad from four skills
let mkQuad : Skill.Skill → Skill.Skill → Skill.Skill → Skill.Skill → Quad =
  λ(a : Skill.Skill) → λ(b : Skill.Skill) → λ(c : Skill.Skill) → λ(d : Skill.Skill) →
    let t1 = mkTriad a b c "quad-left" "Left triad of quad"
    let t2 = mkTriad b c d "quad-right" "Right triad of quad"
    in { triad1 = t1, triad2 = t2, sharedSkill = b }

-- Export all types and functions
in {
  -- Types
  Triad = Triad,
  Pattern = Pattern,
  Quad = Quad,
  
  -- Functions
  triadSum = triadSum,
  isBalanced = isBalanced,
  assertBalanced = assertBalanced,
  mkTriad = mkTriad,
  patternToTrits = patternToTrits,
  mkQuad = mkQuad,
  
  -- Example triads
  unworldFederation = unworldFederation,
  mathVerification = mathVerification,
  modelicaSimulation = modelicaSimulation
}
