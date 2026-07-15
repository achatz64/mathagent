---
name: corecheck
description: Type-check ma1/*.cor files with the native Core checker (corecheck). Use when the user runs /corecheck, or after editing/adding any .cor file to verify it still checks — additionally to the Lean checks from /lean-link. Runs the checker built in checker/ and reports per-file ok/fail.
---

# corecheck

`corecheck` is the repo's native Core type checker (a Lean program built in
`checker/`, exposed on PATH as `corecheck` → `checker/.lake/build/bin/corecheck`).
It models `ma1/core.md` as its own object language and enforces Core-specific
rules the Lean-link path does not — chiefly the lambda-lifting discipline that
declaration head parameters must be supplied all at once (`f X Y` is a valid Core
constant, `f X` is a rejected partial head application).

Use it to verify `.cor` changes **in addition to** the Lean check from
[[lean-link]] — the two catch different things.

## How to run

`corecheck <file.cor>` recursively loads the file's `import` dependencies, checks
them in order, and prints `ok <file>` per checked file. It resolves imports next
to the importing file, then the cwd, then `ma1/`. Run it from `ma1/` and pass the
changed file:

```bash
cd /home/andre/mathagent/ma1
corecheck set_constructions.cor
```

- Exit 0 = all checked files passed (one `ok <file>` line each).
- Non-zero exit = failure; the checker prints `<file>:<line>: <diagnostic>` and
  `uncaught exception: corecheck failed`.

To check the whole live corpus, check the current root file, which pulls in the
rest of the live line via imports (e.g. `classical_first_order_logic_new.cor`,
`set_constructions.cor`).

## Interpreting a failure

The checker is generic: it checks every `.cor` the same way, with no hardcoded
file list. A failure means the file contains something the checker rejects —
either a genuine type error, or (the checker is still incomplete) a construct it
does not yet support.

So a failure is always a real signal, not something to wave off by filename. The
only judgement is whether *your change* caused it: if a file already failed
before you touched it (e.g. an older design-stage file using constructs the
checker has not grown to handle yet), your edit did not introduce that — confirm
by checking the baseline, don't assume any file is "expected" to fail.

## If the binary is missing

Rebuild it, then retry:

```bash
cd /home/andre/mathagent/checker && lake build
```
