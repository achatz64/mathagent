# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

See [OVERVIEW.md](OVERVIEW.md) for the project vision, architecture, and rules. It is the source of truth; this repo is still at the design stage (no code or build/test tooling yet).

## Checking `.cor` changes

Whenever you change, add, or rename a `ma1/*.cor` file, verify it with **both**
checkers before considering the change done:

1. The native Core checker via the `corecheck` skill: `cd ma1 && corecheck <file.cor>`
   (checks the file and its imports; exit 0 and per-file `ok` lines = pass).
2. The Lean checks via the `lean-link` skill (run/re-run it, especially after
   adding or renaming a file, then `lake build`).

The two catch different things, so run both. `corecheck` is generic (no hardcoded
file list) — a failure always means the file has something it rejects, either a
real type error or a construct the still-incomplete checker doesn't yet support.
Treat every failure as a real signal; the only thing to rule out is whether your
change caused it (compare against the baseline — a file that already failed before
you touched it isn't your regression).
