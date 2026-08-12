# Lean REPL

Pi loads `.pi/extensions/lean-repl/` by default. The extension maintains one
project-wide Lean REPL shared by the main SDK session and managed subagents.
It starts the compiled REPL through `lake env`, imports `Mathlib` once, and
serializes all requests through a FIFO queue.

## Basic use

Call `lean_repl` with Lean code in `cmd`. The response includes an environment
number, REPL-generation token, and process ID:

```text
lean_repl({ cmd: "def x : Nat := 37" })
-- { ..., env: 1, repl: "1:48211", pid: 48211 }

lean_repl({ cmd: "#check x", env: 1, repl: "1:48211" })
```

Passing an environment continues from it. Reusing an earlier environment
creates a branch; elaboration does not mutate that earlier environment.
Omitting `env` starts from the shared Mathlib root.

The root has already executed `import Mathlib`. Do not send `import` commands
through the tool: later REPL calls elaborate inside an existing environment,
not at the beginning of a Lean file. The persistent project target is not loaded
into the root; paste any required project-local prerequisites into a branch.
Never use broad `#find` commands in the shared process. Search checked-out
Mathlib source narrowly, then verify exact names with `#check`, `#print`, or
`#synth`.

Always retain and pass `repl` together with an `env` that crosses turns or is
handed to another agent. Bare integer environments remain accepted for
compatibility, but cannot detect that the REPL has restarted. A stale
`repl` token is rejected instead of accidentally addressing an unrelated
environment number.

## Sharing and concurrency

Extension instances acquire reference-counted leases on a process-wide service
keyed by the resolved Lean project directory. Consequently:

- the main agent and all in-process managed subagents see the same environments;
- worker shutdown does not terminate a REPL still leased by another session;
- the final lease release terminates the process;
- only the service writes to stdin, so protocol frames cannot interleave.

Lean elaboration itself is serialized. Agents can reason concurrently, but one
long Lean request delays every queued request. Prefer bounded exploratory
commands and branch from known-good environments. A request timeout or framing failure closes that process because continuing
would be unsafe. The service immediately starts a new generation before
releasing the FIFO queue, so requests still waiting in the queue can continue
against a healthy process. The request that detected the failure receives an
error naming the replacement generation and must retry from the new root.
All environments and generation tokens from the terminated process are stale;
retry without them and re-elaborate any required local declarations.

The PID reported by the tool is the `lake env` owner. The operating system may
also show its actual REPL child; this pair represents one logical shared REPL.
The launcher and child run in their own process group. Closing or replacing a
generation terminates the complete group and waits for it to exit before a new
generation is started; this prevents timed-out children from becoming orphaned
and continuing to consume CPU and memory.

## Monitoring

Every `lean_repl` response includes a `health` object. The separate
`lean_repl_status` tool reports the same information without enqueueing Lean
code:

- generation token and owner PID;
- active lease/reference count;
- active plus queued request count and current active-request age;
- total requests and automatic restart count;
- last restart reason;
- operating-system process-group member count and aggregate RSS on Linux;
- total project REPL processes and any unexpected process-group IDs, which
  exposes orphaned generations directly.

The main agent is responsible for monitoring this state, not merely reacting to
worker reports. Check it before launching multiple Lean workers, at worker
progress checkpoints, after any timeout/restart, and before a build if requests
have recently stalled. A healthy active service normally has one process group
with two members (`lake env` and its REPL child). Investigate immediately if a
generation has more than two members, if old REPL groups remain, if restart
count rises repeatedly, or if `pendingRequests` remains above one while the
active request age approaches the 120-second transport timeout.

When diagnosing latency, inspect both logical and OS state:

```bash
ps -eo pid,ppid,pgid,stat,etime,%cpu,%mem,rss,args \
  | grep -E '[l]ean|[l]ake|repl'
free -h
uptime
```

Do not launch a build or more large replay commands while the shared queue is
backed up. Abort obsolete workers first, let the queue drain, and verify that
only the current process group remains.

## Development and builds

Use the REPL for proof development and API checks. Do not create temporary Lean
files merely to invoke `lake build`. Persistent target files must still receive
a final project build, for example:

```text
cd lean && lake build GT
```

If an integrated build fails, reproduce the failing fragment in `lean_repl`,
fix it there, and only then rebuild.

### Monitored stress builds

A full target build is a stress test of both the proof term and the machine. It
is not enough to observe that it is “still compiling.” Before a diagnostic or
final build:

1. inspect `lean_repl_status` and OS process state;
2. ensure no worker request is active or queued;
3. ensure there are no unexpected REPL process groups;
4. on this memory-constrained host, stop the resident REPL process group before
   a full build when its RSS would materially contend with Lean;
5. run the build with elapsed-time and peak-RSS measurement:

```bash
cd lean
/usr/bin/time -f 'elapsed=%E maxrss=%MKB' lake build GT
```

Use the last committed target as the control. In the March 2026 Coxeter stress
test, the known-good `GT` target built in about 161 seconds as reported by Lake
(about 181 seconds wall time including command overhead) with roughly 3.8 GiB
peak RSS after the REPL was stopped. An unverified integrated proof block raised
memory toward 7 GiB, produced deterministic kernel timeouts, and eventually ran
for more than 15 minutes when `maxHeartbeats` was increased. Restoring the
known-good target immediately restored the baseline. This is a proof-elaboration
regression, not evidence that Mathlib imports are being rebuilt: Lake reported
only the final `GT` job.

If a small proof addition causes a large time/RSS jump, deterministic timeout,
or substantially worse behavior than the control:

- stop the build and inspect the first failing declaration;
- do not compensate by increasing `maxHeartbeats` globally or locally;
- restore the last known-good target before further experiments;
- simplify and validate the suspect declaration in an isolated REPL branch;
- rebuild only after its goals and axiom audit are clean.

The main agent must preserve a buildable target during stress experiments. A
worker's claimed checked block is never justification for repeatedly compiling
a pathological integration.
