# Lean REPL

Pi loads `.pi/extensions/lean-repl.ts` by default. It keeps one `lake exe repl` process for the Pi session and imports `Mathlib` once.

Use `lean_repl` with Lean code in `cmd`. The result contains an `env`; pass that `env` in a later `lean_repl` call to continue from it, or reuse an earlier `env` to branch.

```text
lean_repl({ cmd: "def x : Nat := 37" })
lean_repl({ cmd: "#check x", env: 1 })
```

Omitting `env` starts from the Mathlib root environment.
