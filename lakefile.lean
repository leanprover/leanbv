import Lake
open Lake DSL

package «leanbv» where
  -- add package configuration options here

lean_lib «LeanSatTactic» where
  -- add library configuration options here

@[default_target]
lean_exe «leanbv» where
  root := `Main

-- We let mathlib pick a compatible std library.
-- require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
