import Lake
open Lake DSL

package HashTheory where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib HashTheory where
  srcDir := "."
  roots := #[`HashTheory]

lean_lib IBCCollision where
  srcDir := "."
  roots := #[`IBCCollision]
