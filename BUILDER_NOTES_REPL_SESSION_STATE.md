# Builder record — BUILDER_FEEDBACK_REPL_SESSION_STATE.md (resolved 2026-09-19)

Design decision ratified by user: Option 2, disposable-state-by-design. Issue C
dissolved (no gating mechanism built), per the ratified decision.

## Issue A — env persistence / vanishing batches

Diagnosis: within a live process generation a returned env handle is durable —
the repl records the command snapshot before answering (`recordCommandSnapshot`
in `runCommand`, REPL/Main.lean). The reported vanishing is consistent with the
generation dying (exit(1), plausibly OOM at ~7.6 GB RSS / 9 GB host) right
after the success frame, after which the worker's handle addressed a dead
generation; the bare-env path could then *silently remap* the old env number
onto an unrelated snapshot index of the respawned process — undetectable from
the worker side. That silent remap is now closed:

- Bare `env` without a `repl` token is only accepted when it equals the
  current root environment; anything else is refused loudly
  ("Bare environment N does not address the current root environment M —
  pass env together with the repl token, or omit env ...").
- `env` + `repl` (the documented pair) keeps the existing stale-handle
  rejection across generations.
- Root env handles are stable at 0 per generation (import snapshot), so a
  bare env of 0 keeps working across respawns by design.

Guarantee delivered: "a returned env handle is durable for the lifetime of the
process generation" (verified: branch declarations persist across calls within
a generation, `sessionstate` test), plus loud detection for everything else.

## Issue B — restart-counter semantics

`lean_repl_status` now reports:
- `restarts: {crash, timeout, import}` — per-reason breakdown;
- `recentRestarts` — last 10 events `{reason, at, from, to}` (generation ids);
- `restartCount` unchanged (total).
Reasons: `crash` = respawn after genuine process death (incl. exit(1)/OOM);
`timeout` = request exceeded its time limit, process killed, respawn;
`import` = respawn via `lean_repl_import`. The very first initialization of a
session is not counted as a restart. Workers cannot kill or re-import the
service, so `crash`/`timeout` clusters point at toolchain/payload problems,
not worker misuse. (The reported "19 deliberate restarts" cannot be produced
through worker tools in the current implementation; most plausibly they were
timeout/crash respawns of large calls. If a worker-initiated respawn path is
ever observed again, it is a builder bug — please report with the status
trace.)

## Loud respawn signals

Every `lean_repl` response now carries `generation` (monotonic, alongside
`repl`/`pid`), and status exposes `generation`, the restart breakdown, and the
recent-restart log. A single response is enough to detect a reset by comparing
`repl`/`generation` with the previous call.

## Issue D — memory envelope

exit(1) under a loaded environment (~7.6 GB RSS on 9 GB) is consistent with
OOM; not directly fixable in the service. Documented per-call size guidance in
LEAN_REPL_GENERAL.md ("Session state"): keep single calls moderate (up to a
few hundred lines), prefer sequential batches with persistence spot-checks;
timeout restarts are loud. Per-call timeout remains 120s (deliberate: a
late-arriving frame after a timeout would desynchronize request/response
pairing, so the process is killed and the restart is loud instead).

## Issue C

Dissolved by the ratified decision — no gating built. Automatic respawn on any
request remains; scratch state is disposable by design.

## Verification

- `sessionstate` scenario: durability within generation, loud bare-env
  refusal (non-root and stale), bare root accepted, crash restart counted
  with from/to generation log entry, generation change visible.
- Full regression: healthy / broken (loud failure incl. `Target` now built —
  scenario switched to a genuinely missing module) / cap / stale / already /
  recovery — all pass.
- Fresh `pi -p` end-to-end: bare-env refusal, env+repl pair works, status
  shows generation + restarts.
- Docs updated: LEAN_REPL_GENERAL.md (bare-env semantics, "Session state"
  section, size guidance), LEAN_REPL_MAIN.md ("Restart accounting"),
  lean_repl promptGuidelines.
