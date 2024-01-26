import Lake
open Lake DSL

package «lean2rdf» {
  -- add package configuration options here
}

lean_lib «Lean2rdf» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean2rdf» {
  root := `Main
}
