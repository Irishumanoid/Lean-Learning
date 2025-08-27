import Lake
open Lake DSL

package «LeanLearning» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.21.0"

@[default_target]
lean_lib «LeanLearning» where
  -- Add any library-specific options here
