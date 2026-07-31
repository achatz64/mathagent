# Lean knowledge-base MCP guidance

Before working in this repository, read `OVERVIEW.md`. It is the source of
truth for the project's vision, architecture, and rules.

## `lean-explore` searches

For every `lean-explore` `search` or `search_summary` call, pass
`rerank_top` explicitly and use `0` by default. Never omit it.

When a specific number of usable search results is needed with `rerank_top: 0`,
request a larger `limit`, since generated declarations can be filtered out.

Use a positive `rerank_top` only when the active prompt or harness explicitly
instructs it.

Treat `lean-explore` result IDs as local to the current index and session. Use
them only immediately with detail tools; do not report them to the user unless
asked, and never record them in notes, commits, or issues. Declaration names
(for example, `Nat.add_comm`) are the stable notation: record a name, then
search again for a fresh ID in a later session.

## Host process checks

When asked to inspect running processes or services, do not rely on a
sandboxed `ps` result: it sees only the agent's PID namespace. Run the process
check with host visibility (`sandbox_permissions: "require_escalated"`) unless
the user explicitly asks about sandbox-local processes.
