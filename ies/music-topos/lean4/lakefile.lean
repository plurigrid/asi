import Lake
open Lake DSL

package «music-topos» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib «MusicTopos» where
  globs := #[.submodules `MusicTopos]

lean_exe «tritwise» where
  root := `Main
