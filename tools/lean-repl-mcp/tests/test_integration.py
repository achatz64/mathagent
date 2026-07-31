from __future__ import annotations

import os
import tempfile
import time
import unittest
from pathlib import Path

from lean_repl_mcp.core import (
    InvalidRequestError,
    LeanReplManager,
    StaleEnvironmentError,
    build_settings,
)


TEST_PROJECT = os.environ.get("LEAN_REPL_TEST_PROJECT")


@unittest.skipUnless(TEST_PROJECT, "set LEAN_REPL_TEST_PROJECT for real Lean tests")
class RealLeanIntegrationTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self) -> None:
        assert TEST_PROJECT is not None
        self.project = Path(TEST_PROJECT).expanduser().resolve()
        self.manager = LeanReplManager(
            build_settings(project=self.project, timeout_seconds=60)
        )

    async def asyncTearDown(self) -> None:
        await self.manager.close()

    async def test_real_repl_interaction(self) -> None:
        self.assertIsNone(self.manager.status()["repl_pid"])

        core = await self.manager.check("#check Nat")
        self.assertTrue(core["success"], core)
        self.assertIn("Nat : Type", core["messages"][0]["data"])
        repl_pid = self.manager.status()["repl_pid"]
        self.assertIsNotNone(repl_pid)

        imports = ["Mathlib.Algebra.Group.Basic"]
        cold_started = time.perf_counter()
        declared = await self.manager.check(
            "def transientValue {G : Type} [Group G] (x : G) := x * 1",
            imports=imports,
        )
        cold_seconds = time.perf_counter() - cold_started
        self.assertTrue(declared["success"], declared)
        imported_pid = self.manager.status()["repl_pid"]
        self.assertIsNotNone(imported_pid)
        self.assertNotEqual(imported_pid, repl_pid)
        with self.assertRaises(StaleEnvironmentError):
            await self.manager.check("#check Nat", environment=core["environment"])

        continued = await self.manager.check(
            "#check transientValue", environment=declared["environment"]
        )
        isolated_started = time.perf_counter()
        isolated = await self.manager.check("#check transientValue")
        warm_seconds = time.perf_counter() - isolated_started
        self.assertTrue(continued["success"], continued)
        self.assertFalse(isolated["success"], isolated)
        self.assertEqual(self.manager.status()["repl_pid"], imported_pid)
        self.assertEqual(self.manager.active_imports()["active_imports"], imports)
        self.assertIn(imports, self.manager.status()["cached_import_sets"])

        with self.assertRaises(InvalidRequestError) as raised:
            await self.manager.check(
                "#check Nat", imports=["LeanReplMcp.DoesNotExist"]
            )
        self.assertIn("`LeanReplMcp.DoesNotExist`", str(raised.exception))
        self.assertNotIn("Unknown identifier `True`", str(raised.exception))
        self.assertEqual(self.manager.active_imports()["active_imports"], imports)
        recovered = await self.manager.check("#check Group")
        self.assertTrue(recovered["success"], recovered)

        incomplete = await self.manager.check("example : True := by sorry")
        self.assertTrue(incomplete["success"], incomplete)
        self.assertFalse(incomplete["complete"], incomplete)

        handle = tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".lean",
            prefix="LeanReplMcpTest_",
            dir=self.project,
            delete=False,
        )
        source = Path(handle.name)
        try:
            with handle:
                handle.write("def fileVersionOne := 1\n")
            loaded = await self.manager.load_file(source.name)
            self.assertTrue(loaded["success"], loaded)
            visible = await self.manager.check(
                "#check fileVersionOne", environment=loaded["environment"]
            )
            self.assertTrue(visible["success"], visible)
            source.write_text("def fileVersionTwo := 2\n", encoding="utf-8")
            with self.assertRaises(StaleEnvironmentError):
                await self.manager.check(
                    "#check fileVersionOne", environment=loaded["environment"]
                )
            reloaded = await self.manager.load_file(source.name)
            visible_two = await self.manager.check(
                "#check fileVersionTwo", environment=reloaded["environment"]
            )
            self.assertTrue(visible_two["success"], visible_two)
        finally:
            source.unlink(missing_ok=True)

        print(
            f"real REPL timings: narrow cold={cold_seconds:.3f}s "
            f"cached={warm_seconds:.3f}s",
            flush=True,
        )


if __name__ == "__main__":
    unittest.main()
