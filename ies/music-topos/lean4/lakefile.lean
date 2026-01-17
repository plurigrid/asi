import Lake
open Lake DSL

package MusicTopos where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib MusicTopos where
  -- Only build files with updated Mathlib imports
  -- The *_proved.lean and original files need Mathlib path migration
  srcDir := "."
  roots := #[`MusicTopos]
