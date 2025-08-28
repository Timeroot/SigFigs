import Lake
open Lake DSL

package «SigFigs» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"8bb991a4a08f76e3acc412600e834b09ec9d55b4"

@[default_target]
lean_lib «SigFigs» where
  -- add any library configuration options here
