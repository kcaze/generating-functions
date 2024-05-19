import Lake
open Lake DSL

package «generating-functions» where
  -- add package configuration options here

lean_lib «GeneratingFunctions» where
  -- add library configuration options here

@[default_target]
lean_exe «generating-functions» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
require Paperproof from git
  "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
