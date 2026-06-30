# Lean link

How `.cor` files are type-checked with Lean.

Core is, during this phase, a restricted subset of Lean 4 (see [core.md](core.md)),
so every `.cor` file is valid Lean and can be checked by Lean's type checker. Lean,
however, only recognizes a module if its file ends in `.lean`. We therefore keep a
small Lake project in `lean/` whose `*.lean` files are **symlinks** to the real
`*.cor` sources. Lean reads the content through the symlink; the `.cor` files stay
the single source of truth — nothing is ever copied.

A directory symlink does **not** work: the files inside would still be named
`.cor`, and Lean would not see any modules. Each `.cor` must be mirrored to its own
`.lean` symlink.

```
mathagent/
├── ma1/                         # source of truth (.cor)
│   ├── SK_combinators.cor
│   ├── classical_propositional_logic.cor
│   └── ...
└── lean/                        # Lake project (Lean checks here)
    ├── lean-toolchain
    ├── lakefile.toml
    ├── .gitignore
    ├── SK_combinators.lean      -> ../ma1/SK_combinators.cor   (symlink)
    └── classical_propositional_logic.lean -> ../ma1/classical_propositional_logic.cor
```

## 1. Install / configure (one time)

This is already set up; these are the steps to recreate it from scratch.

1. Create the project folder and pin the Lean toolchain (must be installed via
   `elan`):
   ```bash
   cd mathagent
   mkdir -p lean
   printf 'leanprover/lean4:v4.31.0\n' > lean/lean-toolchain
   ```
2. Create `lean/lakefile.toml`. `srcDir = "."` makes modules resolve relative to
   `lean/`; `roots` lists the modules `lake build` should check (maintained
   automatically by the sync below):
   ```toml
   name = "ma1"
   defaultTargets = ["ma1"]

   [[lean_lib]]
   name = "ma1"
   srcDir = "."
   roots = ["SK_combinators", "classical_propositional_logic"]
   ```
3. Ignore the build output:
   ```bash
   printf '.lake/\n' > lean/.gitignore
   ```
4. Create the symlinks (see §2) and build:
   ```bash
   cd lean && lake build
   ```

### Running Lean

- **VSCode**: open the **`lean/`** folder as the workspace root (`File → Open
  Folder`). The Lean 4 extension activates on `lakefile.toml`. Open any `*.lean`
  symlink to see errors inline and goals in the Infoview.
- **Terminal**: `cd lean && lake build` checks everything; `lake env lean
  <file>.lean` checks one file.

## 2. Maintain it (when files change)

### The easy way: `/lean-link`

After adding, renaming, or deleting any `.cor` file, run the skill:

```
/lean-link
```

It mirrors the whole `ma1` tree to `.lean` symlinks, prunes stale ones,
regenerates `roots`, and runs `lake build`. Idempotent — safe to run any time.

### The manual way

From the repo root, link one new file (`ln -sr` writes a relative symlink):

```bash
ln -srf ma1/NEW_FILE.cor lean/NEW_FILE.lean
```

Then add its module name to `roots` in `lean/lakefile.toml` (the module name is the
path under `ma1/` without `.cor`):

```toml
roots = ["SK_combinators", "classical_propositional_logic", "NEW_FILE"]
```

### Subfolders

Files in subfolders work, but the symlink must mirror the subpath and the module
name uses dots. `ma1/sub/foo.cor` → symlink `lean/sub/foo.lean`, module `sub.foo`,
imported elsewhere as `import sub.foo`, and listed in `roots` as `"sub.foo"`:

```bash
mkdir -p lean/sub
ln -srf ma1/sub/foo.cor lean/sub/foo.lean
```

## After any change: recompile

A new or edited symlink is **not** checked until Lean re-elaborates it.

- **Terminal**: `cd lean && lake build`.
- **VSCode**: editing a file rechecks it automatically. After adding a *new* file
  or changing `roots`, run **`> Lean 4: Restart Server`** (Command Palette) so the
  new module/import is picked up.

Build errors are **real Lean type errors in the `.cor` file** (for example a file
still using the old `have (...)` / `<...>` / `.`-application syntax), not link
problems — fix the `.cor` source.
