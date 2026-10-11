// Regression for BUILDER_FEEDBACK_STALE_OLEAN_RESPAWN.md remedy (builder, 2026-10-10).
// Run: node --experimental-strip-types tmp/regression_stale.mjs
// Uses a lightweight scratch module (import Lean + ScratchStaleTest) instead of
// Mathlib/Target so the whole suite runs in ~2-3 min with modest memory.
import { acquireSharedRepl, staleImportModules } from "../.pi/extensions/lean-repl/service.ts";
import { spawn, execFileSync } from "node:child_process";
import { writeFileSync, utimesSync, unlinkSync, existsSync, rmSync } from "node:fs";
import { join } from "node:path";

const ROOT = "/home/andre/mathagent";
const LEAN = join(ROOT, "lean");
const SCRATCH = "Extlib.ScratchStaleTest";
const scratchLean = join(ROOT, "Extlib", "ScratchStaleTest.lean");
const scratchOLean = join(LEAN, ".lake", "build", "lib", "lean", "Extlib", "ScratchStaleTest.olean");
const BLOCK = `import Lean\nimport ${SCRATCH}`;

let failures = 0;
function check(name, cond, detail = "") {
  console.log(`${cond ? "PASS" : "FAIL"}  ${name}${cond ? "" : ` — ${detail}`}`);
  if (!cond) failures++;
}

// ---------- unit tests: staleImportModules ----------
const probeFile = join(ROOT, "tmp", "stale_unit_probe.olean-fixture");
writeFileSync(probeFile, "x");
utimesSync(probeFile, new Date(Date.now() - 60_000), new Date(Date.now() - 60_000));
const baseEntry = {
  repl: { alive: true },
  loaded: true,
  rootSpawnedAt: Date.now() - 10_000,
  importOLeanPaths: [{ module: "Target", path: probeFile }],
};
check("unit: fresh olean -> []", JSON.stringify(staleImportModules(baseEntry)) === "[]");
check("unit: rebuilt olean -> [Target]", JSON.stringify(staleImportModules({
  ...baseEntry,
  rootSpawnedAt: Date.now() - 120_000,
})) === '["Target"]');
check("unit: missing olean -> [] (not a signal)", JSON.stringify(staleImportModules({
  ...baseEntry,
  importOLeanPaths: [{ module: "Target", path: join(ROOT, "tmp", "no-such.olean") }],
})) === "[]");
check("unit: unresolved paths -> [] (degraded)", JSON.stringify(staleImportModules({
  ...baseEntry,
  importOLeanPaths: undefined,
})) === "[]");
check("unit: dead repl -> []", JSON.stringify(staleImportModules({
  ...baseEntry,
  repl: { alive: false },
})) === "[]");
check("unit: not loaded -> []", JSON.stringify(staleImportModules({
  ...baseEntry,
  loaded: false,
})) === "[]");
unlinkSync(probeFile);

// ---------- integration: real service, real scratch rebuild ----------
function buildScratch(def) {
  writeFileSync(scratchLean, `def ${def} := 1\n`);
  execFileSync("lake", ["build", SCRATCH], { cwd: LEAN, stdio: "ignore" });
}

let lease;
try {
  buildScratch("scratchStaleTestOne");
  lease = acquireSharedRepl(LEAN);

  // 1. fresh import
  const r1 = await lease.initImports(BLOCK);
  check("init: fresh -> initialized", r1 === "initialized", r1);
  const gen1 = lease.generation;

  // 2. unchanged-block re-import with fresh root -> already-running (no-op intact)
  const r2 = await lease.initImports(BLOCK);
  check("no-op: fresh root -> already-running", r2 === "already-running", r2);
  check("no-op: generation unchanged", lease.generation === gen1);

  // 3. status fields
  const s1 = lease.status();
  check("status: rootSpawnedSince set", typeof s1.rootSpawnedSince === "string");
  check("status: staleRootModules empty on fresh root", JSON.stringify(s1.staleRootModules) === "[]", JSON.stringify(s1.staleRootModules));
  const sane = await lease.request("#check scratchStaleTestOne");
  check("sanity: old decl present on fresh root", !JSON.stringify(sane.messages ?? []).includes("error"));

  // 4. BUG REPRODUCTION (deterministic true-positive ordering): the repl reads
  //    each olean at its import position, so a respawn whose import completes
  //    after a fast build would legitimately read the fresh olean. The state
  //    that matters is: generation spawned BEFORE the olean rewrite, root
  //    holding the OLD olean — exactly what the stale-root window produces
  //    (worker request during a build whose olean write lands after the
  //    respawn's read). So: kill, respawn on the old olean, then rebuild.
  execFileSync("kill", ["-TERM", `-${lease.pid}`]);
  const respawn = await lease.request("#check scratchStaleTestOne");
  check("respawn: stale decl still live", !JSON.stringify(respawn.messages ?? []).includes("error"), JSON.stringify(respawn.messages ?? []));
  writeFileSync(scratchLean, `def scratchStaleTestTwo := 2\n`);
  await new Promise((res, rej) => {
    const build = spawn("lake", ["build", SCRATCH], { cwd: LEAN, stdio: "ignore" });
    build.once("exit", (code) => code === 0 ? res() : rej(new Error("scratch build failed")));
  });
  if (!existsSync(scratchOLean)) throw new Error("scratch olean missing after build");

  // 5. remedy 2: status detects the stale root
  const s2 = lease.status();
  check("status: staleRootModules flags rebuilt module", JSON.stringify(s2.staleRootModules) === `["${SCRATCH}"]`, JSON.stringify(s2.staleRootModules));
  check("status: stale-root warning present", s2.warnings.some((w) => w.startsWith("stale root:")), JSON.stringify(s2.warnings));

  // 6. remedy 1: unchanged-block import refuses the stale no-op and respawns
  const r3 = await lease.initImports(BLOCK);
  check("import: stale root -> initialized-stale-reload", r3 === "initialized-stale-reload", r3);
  check("import: new generation spawned", lease.generation > gen1);
  const s3 = lease.status();
  check("status: fresh after reload", JSON.stringify(s3.staleRootModules) === "[]");
  check("status: no stale-root warning after reload", !s3.warnings.some((w) => w.startsWith("stale root:")));
  const fresh = await lease.request("#check scratchStaleTestTwo");
  check("reload: new decl present on reloaded root", !JSON.stringify(fresh.messages ?? []).includes("error"));

  // 7. re-import on the reloaded (fresh) root -> normal no-op again
  const r4 = await lease.initImports(BLOCK);
  check("no-op: reloaded root -> already-running", r4 === "already-running", r4);

  // 8. changed block still refused loudly (existing behavior intact)
  let threw = false;
  try { await lease.initImports("import Mathlib"); } catch { threw = true; }
  check("changed block: loud refusal preserved", threw);
} finally {
  if (lease) await lease.release();
  for (const f of [scratchLean, scratchOLean,
    join(LEAN, ".lake", "build", "lib", "lean", "Extlib", "ScratchStaleTest.ilean"),
    join(LEAN, ".lake", "build", "lib", "lean", "Extlib", "ScratchStaleTest.trace"),
    join(LEAN, ".lake", "build", "lib", "lean", "Extlib", "ScratchStaleTest.olean.hash"),
    join(LEAN, ".lake", "build", "lib", "lean", "Extlib", "ScratchStaleTest.ilean.hash")]) {
    if (existsSync(f)) rmSync(f);
  }
}

console.log(failures === 0 ? "ALL PASS" : `${failures} FAILURE(S)`);
process.exit(failures === 0 ? 0 : 1);