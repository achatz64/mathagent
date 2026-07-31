from __future__ import annotations

import asyncio
import os
import tempfile
import unittest
from pathlib import Path

from lean_repl_mcp.core import (
    InvalidRequestError,
    LeanReplManager,
    ReplProcessError,
    ReplProtocolError,
    ReplTimeoutError,
    Settings,
    StaleEnvironmentError,
    find_project,
)


HERE = Path(__file__).parent.resolve()


class TemporaryLeanProject:
    def __init__(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.path = Path(self._temporary.name).resolve()
        (self.path / "lean-toolchain").write_text(
            "leanprover/lean4:v4.test\n", encoding="utf-8"
        )
        (self.path / "lakefile.toml").write_text(
            'name = "test"\n', encoding="utf-8"
        )
        (self.path / "lake-manifest.json").write_text("{}\n", encoding="utf-8")

    def close(self) -> None:
        self._temporary.cleanup()

    def settings(self, **overrides: object) -> Settings:
        values: dict[str, object] = {
            "project": self.path,
            "lake": HERE / "fake_lake.py",
            "repl": HERE / "fake_repl.py",
            "timeout_seconds": 1.0,
            "max_frame_bytes": 1024 * 1024,
            "max_environments": 64,
        }
        values.update(overrides)
        return Settings(**values)  # type: ignore[arg-type]


class DiscoveryTests(unittest.TestCase):
    def test_project_discovery_walks_up(self) -> None:
        project = TemporaryLeanProject()
        nested = project.path / "a" / "b"
        nested.mkdir(parents=True)
        previous = Path.cwd()
        try:
            os.chdir(nested)
            self.assertEqual(find_project(), project.path)
        finally:
            os.chdir(previous)
            project.close()


class ManagerTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self) -> None:
        self.project = TemporaryLeanProject()
        self.manager = LeanReplManager(self.project.settings())

    async def asyncTearDown(self) -> None:
        await self.manager.close()
        self.project.close()

    async def test_multiline_protocol_and_status(self) -> None:
        result = await self.manager.check("#check Nat")
        self.assertTrue(result["success"])
        self.assertEqual(result["messages"][0]["data"], "Nat : Type")
        status = self.manager.status()
        self.assertIsNotNone(status["repl_pid"])
        self.assertEqual(status["environment_tokens"], 1)

    async def test_isolation_and_explicit_continuation(self) -> None:
        declared = await self.manager.check("def privateName := 1")
        continued = await self.manager.check(
            "#check privateName", environment=declared["environment"]
        )
        isolated = await self.manager.check("#check privateName")
        self.assertTrue(continued["success"])
        self.assertFalse(isolated["success"])

    async def test_imports_accumulate_and_expansion_invalidates_tokens(self) -> None:
        self.assertEqual(
            self.manager.active_imports(),
            {
                "success": True,
                "generation": 0,
                "active_context": "none",
                "active_imports": None,
                "active_file": None,
            },
        )

        first = await self.manager.check("def firstBranch := 1", imports=["Foo"])
        first_generation = self.manager.generation
        first_pid = self.manager.status()["repl_pid"]
        self.assertEqual(first["active_imports"], ["Foo"])

        reused = await self.manager.check("#check Nat")
        self.assertTrue(reused["success"])
        self.assertEqual(self.manager.generation, first_generation)
        self.assertEqual(self.manager.status()["repl_pid"], first_pid)

        expanded = await self.manager.check("#check String", imports=["Bar"])
        self.assertTrue(expanded["success"])
        self.assertGreater(self.manager.generation, first_generation)
        self.assertNotEqual(self.manager.status()["repl_pid"], first_pid)
        self.assertEqual(expanded["active_imports"], ["Bar", "Foo"])
        self.assertEqual(
            self.manager.active_imports()["active_imports"], ["Bar", "Foo"]
        )
        self.assertEqual(
            self.manager.status()["cached_import_sets"], [["Bar", "Foo"]]
        )

        with self.assertRaises(StaleEnvironmentError):
            await self.manager.check(
                "#check firstBranch", environment=first["environment"]
            )

        with self.assertRaises(InvalidRequestError) as raised:
            await self.manager.check("#check Nat", imports=["Missing"])
        self.assertIn("`Missing`", str(raised.exception))
        self.assertNotIn("Unknown identifier `True`", str(raised.exception))
        self.assertEqual(
            self.manager.active_imports()["active_imports"], ["Bar", "Foo"]
        )
        recovered = await self.manager.check("#check Nat")
        self.assertTrue(recovered["success"])
        self.assertEqual(recovered["active_imports"], ["Bar", "Foo"])

    async def test_errors_and_sorries_are_normalized(self) -> None:
        error = await self.manager.check("TYPE_ERROR")
        incomplete = await self.manager.check("theorem t : True := by sorry")
        self.assertFalse(error["success"])
        self.assertTrue(incomplete["success"])
        self.assertFalse(incomplete["complete"])
        self.assertNotIn("environment", error)

    async def test_error_after_diagnostic_limit_still_fails(self) -> None:
        result = await self.manager.check("MANY_WARNINGS_ERROR")
        self.assertFalse(result["success"])
        self.assertTrue(result["truncated"])

    async def test_file_token_becomes_stale_after_edit(self) -> None:
        source = self.project.path / "Current.lean"
        source.write_text("def before := 1\n", encoding="utf-8")
        loaded = await self.manager.load_file("Current.lean")
        visible = await self.manager.check(
            "#check before", environment=loaded["environment"]
        )
        self.assertTrue(visible["success"])
        source.write_text("def after := 2\n", encoding="utf-8")
        with self.assertRaises(StaleEnvironmentError):
            await self.manager.check(
                "#check before", environment=loaded["environment"]
            )
        reloaded = await self.manager.load_file("Current.lean")
        visible_after = await self.manager.check(
            "#check after", environment=reloaded["environment"]
        )
        self.assertTrue(visible_after["success"])

    async def test_file_and_import_contexts_replace_each_other(self) -> None:
        imported = await self.manager.check("#check Nat", imports=["Foo"])
        source = self.project.path / "Current.lean"
        source.write_text("def fromFile := 1\n", encoding="utf-8")

        loaded = await self.manager.load_file("Current.lean")
        self.assertEqual(loaded["active_context"], "file")
        self.assertIsNone(loaded["active_imports"])
        self.assertEqual(loaded["active_file"], "Current.lean")
        with self.assertRaises(StaleEnvironmentError):
            await self.manager.check("#check Nat", environment=imported["environment"])

        checked = await self.manager.check("#check Nat")
        self.assertTrue(checked["success"])
        self.assertEqual(checked["active_context"], "imports")
        self.assertEqual(checked["active_imports"], [])
        self.assertIsNone(checked["active_file"])
        with self.assertRaises(StaleEnvironmentError):
            await self.manager.check(
                "#check fromFile", environment=loaded["environment"]
            )

    async def test_file_must_be_inside_project(self) -> None:
        with tempfile.NamedTemporaryFile(suffix=".lean") as outside:
            with self.assertRaises(InvalidRequestError):
                await self.manager.load_file(outside.name)

    async def test_project_change_invalidates_tokens(self) -> None:
        declared = await self.manager.check("def oldName := 1")
        generation = self.manager.generation
        (self.project.path / "lake-manifest.json").write_text(
            '{"changed": true}\n', encoding="utf-8"
        )
        with self.assertRaises(StaleEnvironmentError):
            await self.manager.check(
                "#check oldName", environment=declared["environment"]
            )
        self.assertGreater(self.manager.generation, generation)

    async def test_local_olean_change_invalidates_tokens(self) -> None:
        declared = await self.manager.check("def oldName := 1")
        build = self.project.path / ".lake" / "build" / "lib" / "lean"
        build.mkdir(parents=True)
        (build / "Local.olean").write_bytes(b"first")
        with self.assertRaises(StaleEnvironmentError):
            await self.manager.check(
                "#check oldName", environment=declared["environment"]
            )

    async def test_timeout_invalidates_and_later_call_restarts(self) -> None:
        self.manager.settings = self.project.settings(timeout_seconds=0.1)
        self.manager.process.settings = self.manager.settings
        generation = self.manager.generation
        with self.assertRaises(ReplTimeoutError):
            await self.manager.check("SLEEP_REPL")
        self.assertGreater(self.manager.generation, generation)
        self.manager.settings = self.project.settings(timeout_seconds=1.0)
        self.manager.process.settings = self.manager.settings
        recovered = await self.manager.check("#check Nat")
        self.assertTrue(recovered["success"])

    async def test_oversized_frame_invalidates_and_recovers(self) -> None:
        self.manager.settings = self.project.settings(max_frame_bytes=512)
        self.manager.process.settings = self.manager.settings
        with self.assertRaises(ReplProtocolError):
            await self.manager.check("HUGE_REPL")
        self.manager.settings = self.project.settings(max_frame_bytes=1024 * 1024)
        self.manager.process.settings = self.manager.settings
        recovered = await self.manager.check("#check Nat")
        self.assertTrue(recovered["success"])

    async def test_crash_invalidates_and_later_call_restarts(self) -> None:
        generation = self.manager.generation
        with self.assertRaises(ReplProcessError):
            await self.manager.check("CRASH_REPL")
        self.assertGreater(self.manager.generation, generation)
        recovered = await self.manager.check("#check Nat")
        self.assertTrue(recovered["success"])

    async def test_concurrent_calls_are_serialized(self) -> None:
        results = await asyncio.gather(
            self.manager.check("#check Nat"),
            self.manager.check("#check String"),
        )
        self.assertEqual(
            [result["messages"][0]["data"] for result in results],
            ["Nat : Type", "String : Type"],
        )

    async def test_manual_reset_changes_generation(self) -> None:
        await self.manager.check("#check Nat")
        generation = self.manager.generation
        result = await self.manager.reset()
        self.assertTrue(result["success"])
        self.assertEqual(self.manager.generation, generation + 1)
        self.assertIsNone(self.manager.status()["repl_pid"])


if __name__ == "__main__":
    unittest.main()
