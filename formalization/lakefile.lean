import Lake
open Lake DSL

package «PaperFormalization» where
  -- Lean package for `post-train-prob-voting/paper/main.tex`.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib PaperFormalization where
  -- keep default library settings
