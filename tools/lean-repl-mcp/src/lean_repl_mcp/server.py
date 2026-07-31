from __future__ import annotations

import argparse
import asyncio
import logging
import os
import sys
from contextlib import asynccontextmanager
from typing import Any, AsyncIterator

from mcp.server.fastmcp import FastMCP

from .core import (
    ConfigurationError,
    LeanReplManager,
    LeanReplMcpError,
    build_settings,
)


LOGGER = logging.getLogger("lean_repl_mcp")


def _error_result(exc: LeanReplMcpError) -> dict[str, Any]:
    return {
        "success": False,
        "complete": False,
        "kind": exc.kind,
        "error": str(exc),
    }


def create_server(manager: LeanReplManager) -> FastMCP:
    @asynccontextmanager
    async def lifespan(_: FastMCP) -> AsyncIterator[dict[str, Any]]:
        warm_task: asyncio.Task[None] | None = None
        if manager.settings.warm_imports:
            warm_task = asyncio.create_task(manager.warm())
        try:
            yield {"manager": manager}
        finally:
            if warm_task is not None and not warm_task.done():
                warm_task.cancel()
                try:
                    await warm_task
                except asyncio.CancelledError:
                    pass
            await manager.close()

    mcp = FastMCP("Lean REPL", lifespan=lifespan, json_response=True)

    @mcp.tool()
    async def lean_check(
        code: str,
        imports: list[str] | None = None,
        environment: str | None = None,
    ) -> dict[str, Any]:
        """Elaborate Lean code using explicit imports or a prior environment.

        Modules in `imports` are added to the cumulative active import base;
        omit `imports` to reuse it. Do not write import commands in `code`.
        Independent calls branch from the active immutable base.
        A successful response contains an opaque `environment` token that can
        be supplied to a later call instead of imports.
        """
        try:
            return await manager.check(code, imports=imports, environment=environment)
        except LeanReplMcpError as exc:
            return _error_result(exc)

    @mcp.tool()
    async def lean_load_file(path: str) -> dict[str, Any]:
        """Elaborate the current contents of a project-relative Lean file.

        The file must resolve inside the configured project. On success the
        response contains an environment token for subsequent `lean_check`
        calls. The token becomes stale if the source file changes.
        """
        try:
            return await manager.load_file(path)
        except LeanReplMcpError as exc:
            return _error_result(exc)

    @mcp.tool()
    async def lean_repl_status() -> dict[str, Any]:
        """Report MCP/REPL identity, warm-up state, caches, and limits."""
        return manager.status()

    @mcp.tool()
    async def lean_repl_active_imports() -> dict[str, Any]:
        """Report the active Lean context and cumulative import modules."""
        return manager.active_imports()

    @mcp.tool()
    async def lean_repl_reset() -> dict[str, Any]:
        """Stop the REPL and invalidate all cached Lean environments."""
        try:
            return await manager.reset()
        except LeanReplMcpError as exc:
            return _error_result(exc)

    return mcp


def _positive_float(value: str) -> float:
    parsed = float(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="lean-repl-mcp",
        description="Expose a project-pinned Lean community REPL over MCP stdio",
    )
    parser.add_argument("--project", help="Lean project directory")
    parser.add_argument("--lake", help="Path to the Lake executable")
    parser.add_argument("--repl", help="Path to the built REPL executable")
    parser.add_argument(
        "--timeout",
        type=_positive_float,
        default=float(os.environ.get("LEAN_REPL_TIMEOUT_SECONDS", "60")),
        help="per-request timeout in seconds (default: 60)",
    )
    parser.add_argument(
        "--max-frame-bytes",
        type=_positive_int,
        default=int(os.environ.get("LEAN_REPL_MAX_FRAME_BYTES", str(5 * 1024 * 1024))),
        help="maximum JSON response frame size (default: 5 MiB)",
    )
    parser.add_argument(
        "--max-environments",
        type=_positive_int,
        default=int(os.environ.get("LEAN_REPL_MAX_ENVIRONMENTS", "256")),
        help="reset after this many REPL environments (default: 256)",
    )
    parser.add_argument(
        "--warm-import",
        action="append",
        default=[],
        metavar="MODULE",
        help="module in the optional asynchronously warmed import set; repeatable",
    )
    parser.add_argument(
        "--log-level",
        choices=("DEBUG", "INFO", "WARNING", "ERROR"),
        default=os.environ.get("LEAN_REPL_MCP_LOG_LEVEL", "WARNING"),
    )
    return parser


def main(argv: list[str] | None = None) -> None:
    args = make_parser().parse_args(argv)
    logging.basicConfig(
        stream=sys.stderr,
        level=getattr(logging, args.log_level),
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )
    try:
        settings = build_settings(
            project=args.project,
            lake=args.lake,
            repl=args.repl,
            timeout_seconds=args.timeout,
            max_frame_bytes=args.max_frame_bytes,
            max_environments=args.max_environments,
            warm_imports=args.warm_import,
        )
    except ConfigurationError as exc:
        LOGGER.error("%s", exc)
        raise SystemExit(2) from exc
    manager = LeanReplManager(settings)
    create_server(manager).run(transport="stdio")


if __name__ == "__main__":
    main()
