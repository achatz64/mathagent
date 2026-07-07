# Core checker

This is an isolated Lean implementation of a native checker for `ma1/core.md`.
It deliberately does not reuse the repository's `lean/` folder: that folder is for
Lean-linking `.cor` files, while this folder models Core as its own object
language.

The first enforced Core-specific rule is the lambda-lifting discipline from
`core.md`: declaration head parameters must be supplied all at once. For example,
if Core contains

```lean
axiom f (X Y : Type) : X -> Y -> X
```

then `f X Y` is accepted as the fully instantiated Core constant, but `f X` is
rejected even though Lean would normally view it as a partial application.

## WSL usage

From the repository root:

```bash
cd checker
lake build
.lake/build/bin/corecheck Examples/good.cor
.lake/build/bin/corecheck Examples/partial.cor
```

`Examples/good.cor` should pass. `Examples/partial.cor` should fail with a
partial-application diagnostic.

For real Core files, run from `ma1/` and pass the target file only:

```bash
cd /home/andre/mathagent/ma1
../checker/.lake/build/bin/corecheck set_constructions.cor
```

The CLI recursively loads `import M` dependencies before checking the requested
file. `import A.B` maps to the relative path `A/B.cor`, resolved against an ordered
list of source roots (analogous to Lean's `LEAN_PATH`):

1. the importing file's own directory (covers the flat sibling layout entirely);
2. the current working directory;
3. roots from the `COREPATH` environment variable (colon-separated);
4. the discovered repository root (the enclosing directory containing `.git`) and
   its `ma1/` subdirectory.

There is no hardcoded absolute path, so the checker is portable across checkouts.

## Current scope

The checker currently implements:

- Core AST for identifiers, holes, `Type`, `Prop`, arrows, products, application,
  and composition.
- A small parser for the Lean-shaped Core surface used by `.cor` files.
- Namespaces, `open`, declarations, abbreviations, and `#check`.
- Recursive `import` loading from the CLI, so users do not need to hand-list
  dependency chains.
- Type checking for application and composition.
- Transparent expansion of Core `abbrev`s.
- The `Prop -> Prop` impredicative arrow rule needed by propositional
  combinators.

The checker is generic: it applies the same rules to every `.cor` file, with no
hardcoded per-file handling. It is not yet complete, though — some constructs it
does not model yet, so files using them are rejected. In particular, older
design-stage files on the SK-combinator path (e.g.
`ma1/classical_propositional_logic.cor`) use constructs the checker has not grown
to handle, so they currently fail; that reflects the checker's coverage, not a
special case for those files. The remaining work is to grow the model/parser to
cover the full corpus while keeping the Core-specific no-partial-head-parameters
rule explicit.
