import RDF

def main : IO Unit := do
  let triples: Array Triple := #[
    ⟨Subject.NamedNode ⟨"http://example.org"⟩, Predicate.NamedNode ⟨"http://example.org"⟩, (1:)⟩
  ]
  IO.println $ RDFSerialize triples "text/turtle"
