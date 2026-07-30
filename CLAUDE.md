# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

Before working in this repository, read [OVERVIEW.md](OVERVIEW.md). It is the
source of truth for the project vision, architecture, and rules.

## Using the `lean-explore` MCP tools

**Always pass `rerank_top` explicitly. Default it to `0`. Never omit it. Use a
positive value only when the active prompt or harness explicitly instructs it.**

`search` and `search_summary` default `rerank_top` to **50** (`lean_explore/mcp/tools.py`, v1.2.1), which runs a Qwen3 cross-encoder over 50 candidates on *every* call. That is recurring per-query CPU work, not a cold start that amortises, and it is the single largest cost of using these tools. There is no way to change the default from outside the call: `lean-explore mcp serve` accepts only `--backend` and `--api-key`, and the package reads no environment variable or config key for reranking. The parameter is the only lever, so omitting it is a decision to rerank.

```jsonc
{ "query": "commutativity of addition", "limit": 10, "rerank_top": 0 }
```

### What `rerank_top` actually does

From `lean_explore/search/engine.py`:

```python
top_n = rerank_top if rerank_top and rerank_top > 0 else limit
scored_results = boosted_scores[:top_n]
if rerank_top and rerank_top > 0:
    return await self._rerank_candidates(query, scored_results, limit)
```

`rerank_top` sets the **candidate pool** — how many RRF hits are considered — and `limit` caps the output. You get whichever is smaller, minus any auto-generated declarations, which are filtered out *after* the pool is cut:

```
results ≤ min(rerank_top or limit, limit)
```

| `rerank_top` | `limit` | pool | results |
|---|---|---|---|
| `5` | `10` | 5 | **≤5** — the pool runs out first |
| `50` | `10` | 50 | **≤10** — `limit` binds |
| `0` | `10` | 10 | **≤10** |

So a small `rerank_top` silently caps your results, and `rerank_top: 0` makes the pool exactly `limit` — in both cases the auto-generated filter can leave you short. **Ask for a larger `limit` than you need.**

With `rerank_top: 0` (or `null`) reranking is skipped entirely, and since `RerankerClient` is built lazily the reranker model is never loaded.

### Declaration `id` is index-local — never persist one

`id` on a search result is a plain SQLite primary key on the `declarations`
table (`lean_explore/models/search_db.py`: `id: Mapped[int] =
mapped_column(Integer, primary_key=True)`), assigned by insertion order. It is
not a hash and carries no information about the declaration. It is unique and
stable *within one built index*, and meaningless outside it: re-fetching the
corpus at a different `--le-data-version` renumbers everything, so a remembered
id may later name a different declaration, or none.

**Within a session, use ids — you have no choice.** The six detail tools
(`get_source_code`, `get_docstring`, `get_source_link`, `get_description`,
`get_module`, `get_dependencies`) take `declaration_id: int` and offer no
by-name lookup. The intended flow is exactly `search_summary` → note the id →
`get_source_code(id)`.

**Across sessions, use the name.** `name` is the stable notation (`unique`,
indexed — e.g. `Nat.add_comm`). Do not report ids to the user unless asked.
Write names into notes, commits, and issues, never ids. To come back to a
declaration later, `search` for the name and take the id from the fresh result.
