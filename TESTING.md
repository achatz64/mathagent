# Testing Pi Extensions from the CLI

Launch a fresh pi process in print mode to test extensions end-to-end without reloading the current session. The model receives the new extension's tools and follows instructions in the prompt.

## Basic pattern

```bash
cd /path/to/project && timeout 120 pi -p --no-context-files "Step 1: call <tool> with args: '<value>'. Step 2: call <tool2> and report the result." 2>&1 | tail -30
```

- `-p` — print mode, non-interactive, exits after completion
- `--no-context-files` — skips AGENTS.md, faster and predictable
- `timeout` — safety net for runaway prompts
- `tail -30` — see the final summary without tool-call spam

## Chaining steps

Give numbered, explicit instructions. The model will execute them sequentially:

```
"Step 1: call lean_repl_import with imports: 'import Mathlib'.
Step 2: call lean_repl with cmd: '#check 1+1' (env: 0).
Step 3: call lean_repl_status and report initialized and restartCount."
```

## When to use

| Scenario | How |
|----------|-----|
| New extension tool — verify it registers and works | Launch fresh process, prompt to exercise the tool |
| Multi-step workflow — init → use → check state | Chain steps in one prompt |
| Error path — verify guards and rejections | Prompt to trigger the error, check message |
| State transitions — kill process, re-init | Use `bash` within the prompt to simulate main-agent actions |
| Comparison — before/after state | Capture output, diff ids or counts |

## No reload required

Unlike `/reload` in an interactive session (which may have stale Node module caches), a fresh `pi -p` process loads everything from disk. Use it as the authoritative test.