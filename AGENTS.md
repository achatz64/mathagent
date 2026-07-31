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

## Lean execution

Use the `lean-repl` MCP tools for Lean code execution. The MCP server owns the
shared persistent REPL; agents and subagents must not start their own REPL,
LeanInteract, or `lake env ... repl` process.

Pass narrow module names through `lean_check`'s `imports` argument. Do not add
`import Mathlib` unless the task specifically requires the complete umbrella
module. The server has one cumulative active import base: omit `imports` to
reuse it, while supplying a missing module extends it, restarts the REPL, and
invalidates every earlier environment token. Use `lean_repl_active_imports` to
inspect the current generation and import set, and group checks that need the
same imports. Use a returned environment token only for an intentional
continuation; ordinary checks branch independently from the active import base.

Use `lean_load_file` to elaborate the current source of a project-local Lean
file. File loading replaces the active import context and invalidates prior
tokens. Importing a changed module by name still reads its compiled `.olean`,
so run an explicit Lake build first when validating downstream imports of
updated modules.

## Host process checks

When asked to inspect running processes or services, do not rely on a
sandboxed `ps` result: it sees only the agent's PID namespace. Run the process
check with host visibility (`sandbox_permissions: "require_escalated"`) unless
the user explicitly asks about sandbox-local processes.
