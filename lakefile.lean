import Lake
open Lake DSL

package "furstenberg_sarkozy" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «FurstenbergSarkozy» where
  -- add any library configuration options here
