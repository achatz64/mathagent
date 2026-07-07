# AGENTS.md

This file provides guidance to Codex (Codex.ai/code) when working with code in this repository.

See [OVERVIEW.md](OVERVIEW.md) for the project vision, architecture, and rules. It is the source of truth; this repo is still at the design stage (no code or build/test tooling yet).

This project lives on WSL. For build/check commands, use the Linux path
`/home/andre/mathagent` through WSL rather than Windows `\\wsl.localhost\...`
paths.

For native Core syntax/type checking of `ma1/*.cor`, use the repo-local
`core-checker` skill and the isolated Lean checker in `checker/`.
