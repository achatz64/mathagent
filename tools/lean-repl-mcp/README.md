# Lean REPL MCP

`lean-repl-mcp` exposes a project-pinned
[`leanprover-community/repl`](https://github.com/leanprover-community/repl)
process as a small MCP server. It does not use Lean's language server and does
not provide search.

See [`../../LEAN_REPL_MCP_PLAN.md`](../../LEAN_REPL_MCP_PLAN.md) for the design,
installation requirements, and acceptance criteria.

## Requirements

- Python 3.10 or newer and `uv`;
- `elan` and Lake;
- a Lean project with `lean-toolchain` and `lakefile.toml` or `lakefile.lean`;
- `leanprover-community/repl` pinned to the project's Lean version and built.

For example, a project using Lean `v4.X.Y` can add this to `lakefile.toml`:

```toml
[[require]]
name = "repl"
git = "https://github.com/leanprover-community/repl"
rev = "v4.X.Y"
```

Then build it from the Lean project:

```bash
lake update repl
lake build repl
```

For a `lakefile.lean`, use the equivalent Lake dependency syntax described in
the full plan.

## Install

During local development:

```bash
uv tool install --editable /path/to/lean-repl-mcp
```

For a non-editable local installation:

```bash
uv tool install /path/to/lean-repl-mcp
```

For Codex, register the resulting command in the repository's
`.codex/config.toml`. Relative paths in this project config are anchored at the
containing `.codex` directory, so `cwd = ".."` starts the server at the
repository root without embedding a checkout-specific absolute path:

```toml
[mcp_servers.lean-repl]
command = "lean-repl-mcp"
args = ["--project", "lean", "--warm"]
cwd = ".."
startup_timeout_sec = 30
tool_timeout_sec = 120
```

The repository must be trusted before Codex loads project-scoped config. The
installed command must also be on the `PATH` inherited by Codex. Other MCP
clients can use the same command and arguments in their own stdio-server
format. Project discovery also supports `LEAN_PROJECT_PATH` and upward search;
the REPL can be overridden with `--repl`/`LEAN_REPL_PATH`, and Lake with
`--lake`/`LEAN_LAKE_PATH`.

## Tools

- `lean_check`: independent checks from one cumulative active import base, or
  continuation from an opaque environment token. Omit imports to reuse the
  base; new modules extend it and invalidate existing tokens;
- `lean_load_file`: elaborate the current contents of a project-local `.lean`
  file, replace the active import context, and return a continuation token;
- `lean_repl_status`: process identity, warm-up, cache, and limit information;
- `lean_repl_active_imports`: lightweight active context, generation, and
  accumulated import information;
- `lean_repl_reset`: stop the process and clear the active context and cached
  environments.

The server never adds `import Mathlib`. Pass `--warm` to warm the empty import
base asynchronously after MCP startup. Repeat `--warm-import MODULE` to warm a
narrow nonempty import set instead; specifying a warm import also enables
warm-up without requiring `--warm`. Import bootstraps are validated before
becoming active; a missing module leaves the prior successful set available for
lazy reload.

## Development run

From a Lean project that already has a built `repl` dependency:

```bash
uv run --project /path/to/lean-repl-mcp \
  lean-repl-mcp --project /path/to/lean-project
```

Use `--help` for discovery overrides and limits. All logs go to stderr because
stdout is reserved for the MCP stdio transport.

## Tests

Core tests need no installed MCP SDK:

```bash
PYTHONPATH=src python -m unittest discover -s tests -v
```

Run the real REPL integration against any configured Lean project:

```bash
LEAN_REPL_TEST_PROJECT=/path/to/lean-project \
  PYTHONPATH=src \
  python -m unittest tests/test_integration.py -v
```

After installing the wrapper, run the real stdio MCP integration with the
Python interpreter from its uv tool environment:

```bash
LEAN_REPL_TEST_PROJECT=/path/to/lean-project \
LEAN_REPL_MCP_COMMAND=/resolved/path/to/lean-repl-mcp \
  python -m unittest tests/test_mcp.py -v
```

## Security

Lean elaboration can execute IO through macros, `run_cmd`, plugins, and related
features. This server avoids shell interpolation, confines file loading to the
selected project, and bounds time and output, but it is not a hostile-code
sandbox.
