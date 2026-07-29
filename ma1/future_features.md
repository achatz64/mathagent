# Collection of ideas

## Gap infra improvements

Context: `lean/test.lean` defines a `gap` axiom — a documented `sorry` carrying a
`reason : String` and a `difficulty : Difficulty` (`trivial | routine | hard |
later | unclear | impossible`). It stays import-free (pure core Lean, no
Mathlib, no `import Lean`). The two ideas below trade that minimalism for
tooling and are deferred until we want them.

### 1. Specify statements

Add a list of statements to `gap` which are sufficient to the proof. Similar to habit in math literature: "from X, Y, and Z, we can deduce...". And similar to Lean tactics like `rw`.  

### 2. Editor warning on every `gap` (yellow squiggle)

The bare axiom is silent — a `gap` typechecks with no visual signal, so open
holes are easy to miss while reading. Give each use an editor diagnostic by
turning `gap` into a custom elaborator (term + tactic) that calls `logWarning`
with the reason and difficulty before emitting `gap …`.

- Requires `import Lean` (pulls in the compiler frontend), which breaks the
  file's import-free property — decide whether a dedicated `Gap.lean` module
  that does the metaprogramming, imported only where wanted, is preferable to
  putting it in the core file.
- Prototype that failed only for lack of `import Lean` is the `elab "gap " …`
  version: warn, then `Term.elabTerm`/`evalTactic` the `gap` application.
- Keep the plain axiom as the fallback so import-free files can still use gaps.

### 3. `gap`-report command (self-reporting open assumptions)

A `#gaps <decl>` command (or a whole-file scan) that walks a declaration's value,
collects every `gap` application, and prints a table of `reason` × `difficulty` ×
source location — i.e. "here is everything this result still assumes." Turns a
file into a self-reporting audit of its own soundness debt, which directly serves
the math-analysis goal (surfacing what a paper's argument leaves unproved).

- Metaprogramming: traverse the `Expr` for `gap` heads and read back the literal
  `String`/`Difficulty` arguments; needs `import Lean`.
- `Difficulty` already `deriving Repr`, so levels print without extra work.
- Natural extensions: sort/filter by difficulty (e.g. list all `impossible`
  gaps as red flags), and aggregate transitively across dependencies so
  `#gaps addition_existence` reports gaps in every lemma it uses.
- Complements `#print axioms` (which only tells you `gap` was used *somewhere*,
  not which reasons/difficulties).
