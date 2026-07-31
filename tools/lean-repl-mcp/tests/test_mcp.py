from __future__ import annotations

import json
import os
import time
import unittest

try:
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
except ModuleNotFoundError:  # Allows core-only tests before installing the MCP SDK.
    ClientSession = None  # type: ignore[assignment,misc]
    StdioServerParameters = None  # type: ignore[assignment,misc]
    stdio_client = None  # type: ignore[assignment]


TEST_PROJECT = os.environ.get("LEAN_REPL_TEST_PROJECT")
TEST_COMMAND = os.environ.get("LEAN_REPL_MCP_COMMAND")


def tool_result(result: object) -> dict[str, object]:
    structured = getattr(result, "structuredContent", None)
    if isinstance(structured, dict):
        # FastMCP wraps structured dict results for compatibility.
        value = structured.get("result", structured)
        if isinstance(value, dict):
            return value
    content = getattr(result, "content", [])
    for item in content:
        text = getattr(item, "text", None)
        if isinstance(text, str):
            value = json.loads(text)
            if isinstance(value, dict):
                return value
    raise AssertionError(f"No JSON object in MCP result: {result!r}")


@unittest.skipUnless(
    TEST_PROJECT and TEST_COMMAND and ClientSession is not None,
    "set LEAN_REPL_TEST_PROJECT and LEAN_REPL_MCP_COMMAND for MCP tests",
)
class McpIntegrationTests(unittest.IsolatedAsyncioTestCase):
    async def test_tools_over_stdio(self) -> None:
        assert TEST_PROJECT is not None
        assert TEST_COMMAND is not None
        parameters = StdioServerParameters(
            command=TEST_COMMAND,
            args=["--project", TEST_PROJECT, "--timeout", "60"],
        )
        async with stdio_client(parameters) as (read, write):
            async with ClientSession(read, write) as session:
                await session.initialize()
                tools = await session.list_tools()
                self.assertEqual(
                    {tool.name for tool in tools.tools},
                    {
                        "lean_check",
                        "lean_load_file",
                        "lean_repl_status",
                        "lean_repl_active_imports",
                        "lean_repl_reset",
                    },
                )

                initial = tool_result(await session.call_tool("lean_repl_status"))
                self.assertIsNone(initial["repl_pid"])
                initial_imports = tool_result(
                    await session.call_tool("lean_repl_active_imports")
                )
                self.assertEqual(initial_imports["active_context"], "none")
                self.assertIsNone(initial_imports["active_imports"])

                checked = tool_result(
                    await session.call_tool(
                        "lean_check", {"code": "#check Nat", "imports": []}
                    )
                )
                self.assertTrue(checked["success"], checked)

                running = tool_result(await session.call_tool("lean_repl_status"))
                self.assertEqual(initial["instance_id"], running["instance_id"])
                self.assertEqual(initial["server_pid"], running["server_pid"])
                self.assertIsNotNone(running["repl_pid"])
                active = tool_result(
                    await session.call_tool("lean_repl_active_imports")
                )
                self.assertEqual(active["active_context"], "imports")
                self.assertEqual(active["active_imports"], [])

                missing = tool_result(
                    await session.call_tool(
                        "lean_check",
                        {
                            "code": "#check Nat",
                            "imports": ["LeanReplMcp.DoesNotExist"],
                        },
                    )
                )
                self.assertFalse(missing["success"], missing)
                self.assertEqual(missing["kind"], "invalid_request")
                self.assertIn(
                    "`LeanReplMcp.DoesNotExist`", str(missing["error"])
                )
                self.assertNotIn("Unknown identifier `True`", str(missing["error"]))
                after_missing = tool_result(
                    await session.call_tool("lean_repl_active_imports")
                )
                self.assertEqual(after_missing["active_imports"], [])
                recovered = tool_result(
                    await session.call_tool("lean_check", {"code": "#check Nat"})
                )
                self.assertTrue(recovered["success"], recovered)

                reset = tool_result(await session.call_tool("lean_repl_reset"))
                self.assertTrue(reset["success"], reset)
                stopped = tool_result(await session.call_tool("lean_repl_status"))
                self.assertIsNone(stopped["repl_pid"])

    async def test_warmup_does_not_block_initialize(self) -> None:
        assert TEST_PROJECT is not None
        assert TEST_COMMAND is not None
        parameters = StdioServerParameters(
            command=TEST_COMMAND,
            args=[
                "--project",
                TEST_PROJECT,
                "--timeout",
                "60",
                "--warm",
            ],
        )
        started = time.perf_counter()
        async with stdio_client(parameters) as (read, write):
            async with ClientSession(read, write) as session:
                await session.initialize()
                initialize_seconds = time.perf_counter() - started
                self.assertLess(initialize_seconds, 5.0)
                status = tool_result(await session.call_tool("lean_repl_status"))
                self.assertIn(status["warm_state"], {"warming", "ready"})
                self.assertEqual(status["warm_imports"], [])
                checked = tool_result(
                    await session.call_tool(
                        "lean_check",
                        {
                            "code": "example : True := by trivial",
                            "imports": [],
                        },
                    )
                )
                self.assertTrue(checked["success"], checked)
                ready = tool_result(await session.call_tool("lean_repl_status"))
                self.assertEqual(ready["warm_state"], "ready")


if __name__ == "__main__":
    unittest.main()
