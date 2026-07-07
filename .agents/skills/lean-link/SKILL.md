---
name: lean-link
description: Sync the ma1/*.cor sources into the lean/ Lake project so Lean can type-check them. Use when the user runs /lean-link or asks to (re)link/register .cor files for Lean checking, after adding/renaming/deleting a .cor file. Mirrors the whole ma1 tree as .lean symlinks, regenerates lakefile roots, and builds.
---

# lean-link

Make every `ma1/**/*.cor` source checkable by Lean. The `lean/` Lake project holds
`.lean` **symlinks** to the real `.cor` files (Lean reads content regardless of
extension; it just requires the `.lean` name). A directory symlink does NOT work —
Lean only sees modules whose file ends in `.lean`, so each `.cor` must be mirrored
to a `.lean` symlink individually. This skill does that for the whole tree at once,
so there is nothing to do per file.

## What it does

1. Mirror: for every `ma1/**/*.cor`, ensure a relative symlink at the matching
   `lean/**/*.lean` (subfolders preserved; `ma1/sub/foo.cor` → `lean/sub/foo.lean`,
   module `sub.foo`).
2. Prune: delete `.lean` symlinks under `lean/` whose `.cor` source no longer
   exists.
3. Regenerate `roots` in `lean/lakefile.toml` from the full set of modules, so
   `lake build` checks all of them.
4. Build and report.

## Run (from the repo root `/home/andre/mathagent`)

```bash
cd /home/andre/mathagent

# 2. prune stale .lean symlinks (only symlinks; never touches lakefile.toml / lean-toolchain)
find lean -type l -name '*.lean' -delete

# 1. mirror every .cor as a relative .lean symlink, collecting module names
mods=()
while IFS= read -r f; do
  rel="${f#ma1/}"; link="lean/${rel%.cor}.lean"
  mkdir -p "$(dirname "$link")"; ln -srf "$f" "$link"
  mods+=("\"${rel%.cor}\"")
done < <(find ma1 -name '*.cor' | sort)

# 3. regenerate roots = [ ... ] (replace whole line, dots = subfolders)
mods_joined=$(IFS=,; echo "${mods[*]}")
sed -i "s|^roots = .*|roots = [${mods_joined//,/, }]|" lean/lakefile.toml

# 4. build
cd lean && lake build
```

## Reporting

Tell the user: which symlinks were created/pruned, the resulting `roots`, and the
`lake build` result. If a file fails to build, the errors are **real Lean type
errors in that `.cor` file** (e.g. a file still using the old `have (...)` /
`<...>` / `.`-application syntax) — surface them; they are not link problems.

## Notes

- `.cor` files stay the single source of truth; only symlinks live in `lean/`.
- After `roots` changes, VSCode may need **`> Lean 4: Restart Server`**.
- Re-running is safe and idempotent; run it any time after adding, renaming, or
  deleting a `.cor` file.
