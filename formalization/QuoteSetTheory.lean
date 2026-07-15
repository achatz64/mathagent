import ContextualHOL.SetTheoryQuote

open ContextualHOL.ProgramC

def main : IO Unit := do
  match ← SetTheoryQuote.quoteSetFile ".." |>.run with
  | .error error => throw (IO.userError error)
  | .ok env =>
      match SetTheoryQuote.deriveTheory env with
      | .error error => throw (IO.userError s!"derivation: {repr error}")
      | .ok derivations =>
          IO.println s!"quoted {env.theory.schemas.length} set theory schemas"
          IO.println s!"constructed {derivations.length} contextual Deriv trees"
          for schema in env.theory.schemas do
            IO.println s!"\n{schema.name}"
            IO.println s!"  schema parameters: {repr schema.parameters}"
            IO.println s!"  object context: {repr schema.objects}"
            IO.println s!"  conclusion: {repr schema.conclusion}"
