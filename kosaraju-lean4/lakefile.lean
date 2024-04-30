import Lake
open Lake DSL

package «kosaraju» where
  -- add package configuration options here

@[default_target]
lean_lib «Kosaraju» where
  -- add library configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

