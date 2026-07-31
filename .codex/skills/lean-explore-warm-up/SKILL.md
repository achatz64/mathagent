---
name: lean-explore-warm-up
description: Warm, inspect, and benchmark this project's local LeanExplore MCP server. Use when the user invokes `/lean-explore-warm-up`, asks to warm LeanExplore, reports slow LeanExplore queries, or before Lean-heavy work where current MCP latency matters.
---

# LeanExplore warm-up

Run the procedure sequentially. Time each MCP request end-to-end with a
monotonic clock; do not substitute a tool-reported time.

Use only the already-attached `lean-explore` MCP tool for all searches. Never
invoke the `lean-explore` CLI as a fallback and never manually start, restart,
or attach another MCP server: either action can create a competing local server
or interfere with the active request. If the MCP search tool is unavailable,
report that the warm-up cannot run in the current session and stop; do not
attempt a substitute benchmark.

1. Warm the server with `lean-explore.search` using
   `query: "commutativity of addition"`, `limit: 10`, and `rerank_top: 0`.
   Allow a slow first request to finish; it may be the documented cold start.
   Report its outcome and elapsed time as cold-start context, but do not apply
   the 5-second warmed-query warning threshold to this request.
2. Inspect the full process tree with
   `ps -eo pid,ppid,etime,stat,comm,args --forest`. Report every
   `lean-explore` process whose arguments include `mcp serve --backend local`.
   Use the project-local `.codex/config.toml` as the source of truth for the
   Codex MCP command and arguments; do not use `.mcp.json` for attribution.
   Identify the configured process from that command and its arguments when
   possible. Report PID, PPID, elapsed time, state, arguments, attribution, and
   any competitors. Never terminate or restart a process.
3. Measure three serial `lean-explore.search` requests, each with `limit: 10`
   and `rerank_top: 0`, for: `Nat.add_comm`, `continuity of a function on a
   compact set`, and `prime number divisibility`.

For each of the three warmed queries in step 3, report its outcome and elapsed
time, then report their median. Apply the 5-second warning threshold only to
these warmed queries: warn for a failure or a successful request at or above 5
seconds, including the measured time and its discrepancy from the 5-second
threshold. Do not warn merely because the initial warm-up request in step 1
takes 5 seconds or longer. Treat results as valid only for the current MCP
session; rerun `/lean-explore-warm-up` after an MCP reconnect, server restart,
or material process-tree change.
