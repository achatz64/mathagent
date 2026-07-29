# Loogle (local, via lean-lsp-mcp) — Test Report

Report for 4 AMD CPUs + 16 GB vm.

## Connection status
`lean-lsp-mcp` required a manual `/mcp` reconnect twice this session — once because `.mcp.json` wasn't loaded at session start, once after killing an orphaned sibling session's process took down this session's own `lean-lsp-mcp` too (cause not fully isolated, but likely shared on-disk index file contention — see Memory section).

## Latency

| Scenario | Time | Notes |
|---|---|---|
| First query in a fresh session (cold start) | **7.3s** (range 7–40s observed across tests) | One-time cost: spawns subprocess, loads full elaborated Mathlib environment |
| Warm query, no contention | **0.02s – 0.9s** | Reproducible once isolated |
| Warm query, competing sibling session active | **10.7s** | Same "warm" query, but CPU-contended by a second session's loogle process — see Memory section |

Contrast with lean-explore (semantic, `rerank_top: 0`): ~0.6–1s steady state, no cold-start cliff. Loogle is faster once warm but has a real one-time tax lean-explore doesn't.

## Query quality (structural/syntactic search, not semantic)

Loogle requires its own query DSL — natural language fails outright:
- `"conjugate Sylow subgroups"` → `Unknown identifier 'conjugate'`
- `"existence of Sylow p-subgroups"` → same class of error

Correctly-phrased queries are precise, with zero noise observed:

| Query type | Example | Result |
|---|---|---|
| Bare identifier | `Sylow` | 8 correct hits (definition + basic API) |
| Comma filter (constant + name substring) | `Sylow, "conj"` | 2/2 hits genuinely about conjugation |
| Conclusion-shape pattern | `\|- Nat.card (Sylow _ _) ≡ 1 [MOD _]` | **exactly 1 hit**: `card_sylow_modEq_one` (Sylow's 3rd Theorem) |
| Non-linear metavariable pattern | `Real.sqrt ?a * Real.sqrt ?a` | 1 hit: `Real.mul_self_sqrt`, metavariable correctly unified on both occurrences |
| Conclusion pattern, hypotheses reordered | `\|- _ < _ → tsum _ < tsum _` | 4 hits across `ENNReal`/`NNReal`/`Real`, matched despite hypothesis order differing from the query — confirms documented reorder-tolerant matching |
| Arithmetic subexpression | `(List.replicate (_ + _) _ = _)` | 3 correct hits: `List.replicate_succ`, `_succ'`, `_add` |
| Curried function-type pattern | `(?a -> ?b) -> List ?a -> List ?b` | Found `List.map` plus 4 near-neighbors (`mapTR`, `modify`, etc.) — good precision |

Net: when you know roughly what shape you're looking for, Loogle beats lean-explore on precision. It cannot help with a vague conceptual question.

## Bug found: bare high-hit-count name-substring queries silently fall back to a broken remote endpoint

**Symptom**: `lean_loogle` with query `"differ"` (bare quoted substring, no other filter) reliably fails:
```
Error executing tool lean_loogle: loogle error:
<urlopen error [Errno 111] Connection refused>
```
Reproducible on demand, not a one-off.

**Root cause, traced through source**:
1. The raw `loogle` binary handles `"differ"` fine — 0.85s, valid JSON, **1,811 matches, 200 shown, 83,055-character response line**.
2. `lean_lsp_mcp/loogle.py`'s `LoogleManager.query()` reads that response via `asyncio.StreamReader.readline()` with no custom `limit=` set on the subprocess pipes — so it uses asyncio's **default 64KiB (65,536-byte) line-length limit**. An 83KB response exceeds that, causing an `asyncio.LimitOverrunError`.
3. That exception isn't one of the two specifically handled in `query()` (`asyncio.TimeoutError`, `json.JSONDecodeError`), so it propagates up.
4. `lean_lsp_mcp/tools/search.py:207-208` catches it with a bare `except Exception`, logs "Local loogle failed... falling back to remote," and calls `loogle_remote()`.
5. `loogle_remote()` hits `config.loogle_url()`, which resolves to this repo's `.mcp.json` value — **`LOOGLE_URL=http://127.0.0.1:1`**, a nonsense placeholder (port 1, nothing listens there). Hence `Connection refused`.

**Practical trigger**: any bare name-substring query whose match count is large enough to blow past 200 truncated hits into an oversized JSON line. Narrower queries (add a constant filter, e.g. `Sylow, "conj"`) stay small and work fine — only happened to us on `"differ"` (1,811 matches) among the queries tested.

**Impact**: confusing error message (looks like a network/config problem) instead of a clear "response too large" error, and the fallback path is guaranteed to fail in this repo's current config regardless, since the placeholder URL was seemingly set deliberately to disable remote fallback (possibly to force local-only and avoid the public rate limit) — but that means this failure mode has **no working fallback at all** right now.

**Not something to patch in the installed package casually** (third-party tool) — but worth knowing: avoid bare, broad name-substring queries; add a second filter term to keep hit counts low, or use `--max-results` awareness (loogle's own default cap is 200 hits, but the JSON payload for 200 hits can still overflow the pipe buffer).

## Memory — multi-session risk (source-confirmed, not just observed)

Found an explicit comment in `lean_lsp_mcp/server.py`:
> "Heavy resources like the local loogle subprocess (~6 GB RSS for the Mathlib index) must be initialised exactly once and shared across sessions; otherwise N concurrent clients would spawn N loogle processes and exhaust memory."

The maintainers built a shared-singleton guard (`_shared_loogle_manager`, asyncio lock) for this — **but it only dedupes concurrent sessions within one server process** (relevant to the `streamable-http` transport). Our `.mcp.json` uses `"type": "stdio"`, so **every Claude Code session spawns its own separate `lean-lsp-mcp` OS process**, each with its own independent ~6.5GB loogle subprocess — the singleton guard never engages across sessions in this configuration. This is exactly what we hit earlier: two sessions, two 6.5GB loogle processes, ~20GB combined demand on a 16GB box.

Current state (single session, verified clean):
```
free -h: 1.7Gi used, 13Gi available
```

## Summary / recommendations
1. **Cold start is unavoidable per-session** (~7–40s) — budget for it on the first query.
2. **Warm queries are fast and precise** (~0.02–0.9s) when phrased in Loogle's DSL; use it for "I know the shape/name" lookups, lean-explore for "I don't know what this is called."
3. **Avoid bare broad name-substring queries** (`"word"` alone) until/unless the underlying `lean-lsp-mcp` bug is fixed upstream — add a second comma-separated filter to keep result size down.
4. **Never run two Claude Code sessions with `lean-lsp-mcp --loogle-local` against this repo at once** — no cross-process guard exists; it will double memory usage and risk OOM. Confirmed by both observation and source comment.
5. Swap is still not configured on this box (`Swap: 0B`) — still recommended as a safety net given point 4 is easy to hit accidentally (e.g. forgetting a stale session is open, as happened this session).
