import Lake
open Lake DSL

require Mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

package lean4bits {
  -- add package configuration options here
}

lean_lib Lean4bits {
  -- add library configuration options here
}

@[default_target]
lean_exe lean4bits {
  root := `Main
}
