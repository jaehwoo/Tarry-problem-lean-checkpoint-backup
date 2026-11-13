import Lake
open Lake DSL

package tarrySecondPortfolio where
  leanOptions := #[⟨`maxHeartbeats, .ofNat 200000⟩, ⟨`maxRecDepth, .ofNat 512⟩]
  moreLeanArgs := #["-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c44e0c8ee63ca166450922a373c7409c5d26b00b"

lean_lib PaperILean where
  globs := #[.submodules `PaperILean]

@[default_target]
lean_lib Repro where
  roots := #[`Repro.Endpoints]
