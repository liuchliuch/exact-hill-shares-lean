import Lake
open Lake DSL

package exactHillShares where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib ExactHillShares

lean_lib Tests

lean_lib Challenge where
  globs := #[.submodules `Challenge]

lean_lib Solution where
  globs := #[.submodules `Solution]
