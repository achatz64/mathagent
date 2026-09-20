# Builder issue: REPL OOM-killed by concurrent lake builds (crash family, 8×/45 min)

Reported by: main formalization agent (FT session, 2026-09-19)

## Issue

Eight crash-respawns of the shared REPL occurred between 19:17 and 20:03
(generations 3→10, `crash` reasons, `lastRestartReason: Lean REPL exited
(SIGKILL)`), spaced 5–10 minutes apart. The correlation with main's activity
is unambiguous: that window is exactly when main integrated six worker blocks
into lean/Target.lean, running `lake build Target` after each append. Each
build re-elaborates the (now ~4400-line) target file against Mathlib — a
transient multi-GB allocation — while the resident REPL holds ~7.4 GB RSS on a
9.9 GB host. The kernel OOM killer targets the largest process: the REPL.
Worker conclusions:

- Each crash destroys every live worker branch (disposable-state-by-design,
  correct behavior) and forces full re-elaboration — the dominant credit cost
  of chapter 2 (one 18-hour worker session died re-elaborating, then lost its
  final delivery to a truncated last message).
- Worker load alone was NOT the trigger: the same crash cadence appeared
  during a 2-worker phase whose only other variable was main's build cadence.
- Not fixable via oom_score_adj (protected lowering needs CAP_SYS_RESOURCE;
  verified), no user systemd bus (systemd-run --user fails; verified), no
  cgroup memory limit present.

## Goal

Make lake builds and the resident REPL coexist on this host. Candidate
remedies, builder's choice:

1. (System-level, likely user action) An OOM preference mechanism that spares
   the REPL: e.g. earlyoom/oomd configured to prefer `lake`/build processes,
   or a privileged wrapper that sets oom_score_adj on the repl process group
   at spawn.
2. (Builder-side) Have the extension detect a concurrent heavy build (lean
   process with large RSS not in the repl group) and expose it in
   lean_repl_status warnings ("a build is running; respawn risk elevated") so
   main can sequence builds between worker waves.
3. (Builder-side) Optionally cap build-side memory so the OOM victim is the
   build (cheap to retry) rather than the repl.

Main-side discipline already adopted (no code needed): no `lake build` while
workers hold live branches; integration appends are batched and built once per
wave.
