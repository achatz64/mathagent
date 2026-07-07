---
name: core-checker
description: Run the native Lean-based Core checker in checker/ for ma1/*.cor syntax/type checking. Use when the user asks to type check Core, syntax check Core, run the checker, validate .cor files independently of Lean-linking, or investigate Core lambda-lifting / full-head-parameter errors. This project lives on WSL; run commands from /home/andre/mathagent through WSL, not Windows paths.
---

# core-checker

Use the native Core checker in `checker/`. This is distinct from `lean-link`:
`lean-link` asks Lean to elaborate `.cor` files as Lean modules, while
`core-checker` checks Core's own object language and enforces Core-specific rules
such as "all declaration head parameters must be supplied."

## Environment

This repo is on WSL. Prefer Linux paths and WSL execution:

```bash
cd /home/andre/mathagent
```

From Codex on Windows, run via:

```powershell
wsl -d Ubuntu -- bash -lc 'cd /home/andre/mathagent && ...'
```

Avoid relying on `\\wsl.localhost\...` paths for Lake/Lean commands.

## Build

```bash
cd /home/andre/mathagent/checker
lake build
```

## Run Fixtures

```bash
cd /home/andre/mathagent/checker
.lake/build/bin/corecheck Examples/good.cor
.lake/build/bin/corecheck Examples/partial.cor
```

Expected:

- `Examples/good.cor` passes.
- `Examples/partial.cor` fails with a partial-application diagnostic.

## Run On Core Files

Run from `ma1/` and pass the target file only. The checker reads `import M`
commands and checks dependencies first.

```bash
cd /home/andre/mathagent/ma1
../checker/.lake/build/bin/corecheck set_constructions.cor
```

Import resolution checks paths next to the importing file, then the current
directory, then `ma1/`, then `/home/andre/mathagent/ma1`.

For unusual debugging, explicit dependency lists still work, and already-checked
files are skipped.
Do not assume every `.cor` file is meant to pass: some old design-stage files are
expected to fail.

## Reporting

Report:

- The exact command target set.
- Which files passed.
- Failing file, line, and diagnostic.
- Whether the failure is a Core checker limitation, an expected old-file failure,
  or a likely real `.cor` issue when that can be inferred from context.

Do not modify `.cor` files merely to make a checker run pass unless the user
explicitly asks for source fixes.
