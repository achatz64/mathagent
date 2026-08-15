# Extlib — Builder Documentation

## Adding a new book/paper

1. **Place the file** at `Extlib/<Domain>/<Auth><YY><AdditionalIdentifier>.lean`:
   - `<Domain>` — Mathlib-style folder (`GroupTheory`, `Algebra`, `NumberTheory`, …). Create if needed.
   - `<Auth>` — first 3 letters of the *original* mathematicians' surname, camelCase (e.g. `Mil` for Milne, `Ser` for Serre) ordered alphabetically.
   - `<YY>` — 2‑digit publication year (e.g. `21` for 2021).
   - `<AdditionalIdentifier>` - parts of the title or similar.

   Example: `Extlib/GroupTheory/Mil21.lean`

2. **Compile** from the `lean/` workspace:
   ```bash
   cd lean && lake build Extlib
   ```
   The `globs = ["Extlib.+" ]` in `lean/lakefile.toml` auto-discovers the new file. It compiles using `lean/`'s existing Mathlib oleans — no separate mathlib clone, no extra dependency work. The olean lands at `lean/.lake/build/lib/lean/Extlib/<Domain>/<Auth><YY><AdditionalIdentifier>.olean`.

That's it. No umbrella file, no manual imports in the book itself, no path configuration.
