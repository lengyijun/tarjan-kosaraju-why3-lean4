import Lake
open Lake DSL

package «kosaraju» where
  -- add package configuration options here

@[default_target]
lean_lib «Kosaraju» where
  -- add library configuration options here
lean_lib «Tarjan» where
lean_lib «ListHelper» where
lean_lib «Graph» where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
