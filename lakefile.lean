import Lake
open Lake DSL

package goldbach where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "9837ca9d65d9de6fad1ef4381750ca688774e608"

@[default_target]
lean_lib Goldbach
