import Lake
open Lake DSL

package HorizonMT where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib HorizonMT where
  roots := #[`HorizonMT]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"
