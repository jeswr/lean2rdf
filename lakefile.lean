import Lake
open Lake DSL

package «lean2rdf» {
  -- add package configuration options here
}

lean_lib «Lean2rdf» {
  -- add library configuration options here
}

-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4"

require RDF from git
  "https://github.com/jeswr/RDF.lean" @ "main"

@[default_target]
lean_exe «lean2rdf» {
  root := `Main
}
