import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { existsSync, readdirSync, readFileSync, readlinkSync } from "node:fs";
import { join, resolve } from "node:path";

type ReplRequest = { cmd: string; env?: number };
export type ReplResponse = Record<string, unknown> & { env?: number };

type Waiter = { resolve: (frame: string) => void; reject: (error: Error) => void };

// The root environment (import block + readiness probes) can take minutes to
// load Mathlib, Extlib, and the target; worker requests default to 120s.
const ROOT_TIMEOUT_MS = 600_000;
const PROBE_TIMEOUT_MS = 120_000;
// After this many consecutive failed root initializations, automatic recovery
// stops respawning and fails fast with REPL-DOWN until the main agent
// intervenes (lean_repl_import resets the counter).
const MAX_CONSECUTIVE_INIT_FAILURES = 3;
// How long a pid of our own closed/dying generation is excused from the
// foreign-generation guard (teardown races must not self-refuse a respawn).
const CLOSED_PID_GRACE_MS = 20_000;

type ReplMessage = { severity?: string; data?: string };

function errorMessages(response: ReplResponse): ReplMessage[] {
  const messages = response.messages;
  if (!Array.isArray(messages)) return [];
  return messages.filter(
    (m): m is ReplMessage =>
      !!m && typeof m === "object" && !Array.isArray(m) && m.severity === "error",
  );
}

function formatMessages(messages: ReplMessage[]): string {
  return messages
    .map((m) => m.data ?? JSON.stringify(m))
    .join("; ")
    .slice(0, 2000);
}

/** Module names from an import block: `import Mathlib\nimport Target` → ["Mathlib", "Target"]. */
function parseImportModules(imports: string): string[] {
  const modules: string[] = [];
  for (const match of imports.matchAll(/^import\s+(\S+)/gm)) {
    const name = match[1];
    if (/^[\w.'!?$§Ωα-ωµ]+"?(\.[\w.'!?$§Ωα-ωµ]+"?)*$/.test(name)) modules.push(name);
  }
  return modules;
}

/**
 * Probe that fails (with IMPORT-MISSING) unless every module of the import
 * block is present in the environment header. The repl binary reports failed
 * imports silently (no messages, env counter still advances), so the probe is
 * the only reliable readiness signal.
 */
function buildModuleProbe(modules: string[]): string {
  const names = modules.map((m) => "`" + m).join(",");
  return [
    "#eval show Lean.Elab.Command.CommandElabM Unit from do",
    "  let env <- Lean.getEnv",
    `  let missing := (#[${names}] : Array Lean.Name).filter fun m => !env.header.moduleNames.contains m`,
    "  unless missing.isEmpty do",
    "    Lean.throwError (\"IMPORT-MISSING: \" ++ String.intercalate \", \" (missing.toList.map fun m => m.toString))",
  ].join("\n");
}

class SharedRepl {
  readonly id: string;
  readonly generation: number;
  readonly pid: number | undefined;
  private readonly child: ChildProcessWithoutNullStreams;
  private readonly exited: Promise<void>;
  private buffer = "";
  private frames: string[] = [];
  private waiters: Waiter[] = [];
  private serial: Promise<void> = Promise.resolve();
  private rootPromise: Promise<number> | undefined;
  private closed = false;
  readonly imports: string;

  get alive(): boolean { return !this.closed && this.child.exitCode === null; }

  constructor(cwd: string, imports: string, generation: number) {
    this.imports = imports;
    const binary = join(cwd, ".lake", "packages", "repl", ".lake", "build", "bin", "repl");
    const options = { cwd, stdio: ["pipe", "pipe", "pipe"] as const, detached: true };
    this.child = existsSync(binary)
      ? spawn("lake", ["env", binary], options)
      : spawn("lake", ["exe", "repl"], options);
    this.pid = this.child.pid;
    this.generation = generation;
    this.id = `${generation}:${this.pid ?? "pending"}`;
    this.exited = new Promise<void>((resolveExit) => {
      this.child.once("exit", () => resolveExit());
    });
    this.child.stdout.setEncoding("utf8");
    this.child.stdout.on("data", (chunk: string) => this.receive(chunk));
    this.child.once("error", (error) => this.fail(error));
    this.child.once("exit", (code, signal) => {
      this.closed = true;
      this.fail(new Error(`Lean REPL exited (${signal ?? code ?? "unknown"})`));
    });
  }

  /**
   * Root environment number, only returned after the import block has been
   * verified by readiness probes. Failed imports are silent in the repl
   * protocol, so a bare import response proves nothing on its own.
   */
  rootEnvironment(): Promise<number> {
    this.rootPromise ??= this.initializeRoot().catch((error) => {
      this.rootPromise = undefined; // allow a later retry to re-initialize
      throw error;
    });
    return this.rootPromise;
  }

  private async initializeRoot(): Promise<number> {
    const importResponse = await this.requestRaw({ cmd: this.imports }, ROOT_TIMEOUT_MS);
    if (typeof importResponse.env !== "number") {
      throw new Error("Import block returned no environment");
    }
    const root = importResponse.env;
    // Failed imports are silent in the repl protocol (no messages, env counter
    // still advances) and leave an empty, partly-corrupted session. Both
    // probes below are therefore strict: any error means the root is unusable.
    // The availability probe requires the import block to bring in Lean itself
    // (true for every supported block: Mathlib + project modules).
    const availability = await this.requestRaw(
      { cmd: "#check @Lean.Elab.Command.CommandElabM", env: root },
      PROBE_TIMEOUT_MS,
    );
    const availabilityErrors = errorMessages(availability);
    if (availabilityErrors.length > 0) {
      throw new Error(
        "Root environment failed its readiness probe: Lean is unavailable after the import block " +
        "(the repl reports failed imports silently — usually a module without a built .olean; " +
        `run 'cd lean && lake build' for every imported module). Probe errors: ${formatMessages(availabilityErrors)}`,
      );
    }
    const modules = parseImportModules(this.imports);
    if (modules.length > 0) {
      const probeResponse = await this.requestRaw(
        { cmd: buildModuleProbe(modules), env: root },
        PROBE_TIMEOUT_MS,
      );
      const probeErrors = errorMessages(probeResponse);
      if (probeErrors.length > 0) {
        throw new Error(
          `Root environment failed its readiness probe: the import block did not load. ` +
          `Probe errors: ${formatMessages(probeErrors)}`,
        );
      }
    }
    return root;
  }

  async request(cmd: string, env?: number, timeoutMs = 120_000): Promise<ReplResponse> {
    const root = env ?? await this.rootEnvironment();
    return this.requestRaw({ cmd, env: root }, timeoutMs);
  }

  async close(): Promise<void> {
    if (this.closed) return;
    this.closed = true;
    this.fail(new Error("Lean REPL closed"));
    const pid = this.child.pid;
    if (pid === undefined) return;
    try {
      process.kill(-pid, "SIGTERM");
    } catch {
      this.child.kill("SIGTERM");
    }
    const stopped = await Promise.race([
      this.exited.then(() => true),
      new Promise<false>((resolveTimeout) =>
        setTimeout(() => resolveTimeout(false), 2_000)),
    ]);
    if (!stopped) {
      try { process.kill(-pid, "SIGKILL"); } catch { /* already exited */ }
      await Promise.race([
        this.exited,
        new Promise<void>((resolveTimeout) => setTimeout(resolveTimeout, 500)),
      ]);
    }
  }

  private async requestRaw(request: ReplRequest, timeoutMs = 120_000): Promise<ReplResponse> {
    const previous = this.serial;
    let release!: () => void;
    this.serial = new Promise<void>((resolveSerial) => { release = resolveSerial; });
    await previous;
    try {
      if (this.closed || !this.child.stdin.writable) throw new Error("Lean REPL is not running");
      this.child.stdin.write(`${JSON.stringify(request)}\n\n`);
      const frame = await this.nextFrame(timeoutMs);
      const response: unknown = JSON.parse(frame);
      if (!response || typeof response !== "object" || Array.isArray(response)) {
        throw new Error("Lean REPL returned a non-object JSON response");
      }
      return response as ReplResponse;
    } catch (error) {
      await this.close();
      throw error;
    } finally {
      release();
    }
  }

  private receive(chunk: string): void {
    this.buffer += chunk;
    while (true) {
      const match = this.buffer.match(/\r?\n\r?\n/);
      if (!match || match.index === undefined) return;
      const frame = this.buffer.slice(0, match.index);
      this.buffer = this.buffer.slice(match.index + match[0].length);
      const waiter = this.waiters.shift();
      if (waiter) waiter.resolve(frame);
      else this.frames.push(frame);
    }
  }

  private nextFrame(timeoutMs: number): Promise<string> {
    if (this.frames.length > 0) return Promise.resolve(this.frames.shift()!);
    return new Promise<string>((resolveFrame, reject) => {
      const timer = setTimeout(() => {
        const index = this.waiters.findIndex((waiter) => waiter.resolve === resolveFrame);
        if (index >= 0) this.waiters.splice(index, 1);
        reject(new Error(`Lean REPL request exceeded ${timeoutMs / 1000}s`));
      }, timeoutMs);
      this.waiters.push({
        resolve: (frame) => { clearTimeout(timer); resolveFrame(frame); },
        reject: (error) => { clearTimeout(timer); reject(error); },
      });
    });
  }

  private fail(error: Error): void {
    const waiters = this.waiters;
    this.waiters = [];
    for (const waiter of waiters) waiter.reject(error);
  }
}

export type SharedReplStatus = {
  id: string;
  pid: number | undefined;
  references: number;
  pendingRequests: number;
  activeForMs: number | undefined;
  totalRequests: number;
  restartCount: number;
  lastRestartReason: string | undefined;
  generation: number | undefined;
  restarts: Record<RestartReason, number>;
  recentRestarts: RestartEvent[];
  processGroupMembers: number;
  processGroupRssKiB: number;
  projectReplProcesses: number;
  unexpectedProcessGroups: number[];
  warnings: string[];
  initialized: boolean;
  /** True only after the root environment passed its readiness probes. */
  loaded: boolean;
  imports: string | undefined;
  downSince: string | undefined;
  consecutiveInitFailures: number;
  lastInitError: string | undefined;
};

type RestartReason = "crash" | "timeout" | "import";
type RestartEvent = { reason: RestartReason; at: string; from: string | undefined; to: string };

type RegistryEntry = {
  repl: SharedRepl | undefined;
  imports: string | undefined;
  loaded: boolean;
  downSince: number | undefined;
  spawnFailures: number;
  lastInitError: string | undefined;
  restarts: Record<RestartReason, number>;
  restartLog: RestartEvent[];
  everSpawned: boolean;
  /** pid -> closed-at ms of our own generations, excused from the conflict guard. */
  closedPids: Map<number, number>;
  references: number;
  serial: Promise<void>;
  pendingRequests: number;
  activeSince: number | undefined;
  totalRequests: number;
  restartCount: number;
  lastRestartReason: string | undefined;
  projectDir: string;
};
type Registry = { generation: number; entries: Map<string, RegistryEntry> };
const registryKey = Symbol.for("mathagent.shared-lean-repl.registry");
const globals = globalThis as typeof globalThis & { [registryKey]?: Registry };
const registry = globals[registryKey] ??= { generation: 0, entries: new Map() };

export type SharedReplLease = {
  readonly id: string;
  readonly generation: number | undefined;
  readonly pid: number | undefined;
  request(cmd: string, env?: number, replId?: string): Promise<ReplResponse>;
  initImports(imports: string): Promise<"initialized" | "already-running">;
  status(): SharedReplStatus;
  release(): Promise<void>;
};

/** True when a process is a repl of the given project (any path form). */
function isProjectReplProcess(cwd: string, cmdline: string, projectDir: string): boolean {
  if (cwd !== projectDir) return false;
  // The service spawns the repl with an absolute path; hand-launched copies
  // may use a path relative to the project dir. The cwd check above already
  // pins the process to this project.
  return cmdline.includes(".lake/packages/repl/.lake/build/bin/repl");
}

type ForeignGroup = { group: number; pids: number[]; rssKiB: number };

/**
 * REPL processes of OTHER sessions in the project (or leaked orphans): any
 * repl-cmdline process in the project dir whose process group is neither our
 * live generation nor one of our recently closed ones. Each loaded generation
 * holds ~7.6 GB, so more than one on a host is an OOM regime — spawns are
 * refused while a foreign generation exists.
 */
function foreignReplGroups(
  projectDir: string,
  ownPid: number | undefined,
  closedPids: Map<number, number>,
): ForeignGroup[] {
  if (process.platform !== "linux") return [];
  const now = Date.now();
  for (const [closedPid, at] of closedPids) {
    if (now - at > CLOSED_PID_GRACE_MS) closedPids.delete(closedPid);
  }
  const byGroup = new Map<number, ForeignGroup>();
  try {
    for (const name of readdirSync("/proc")) {
      if (!/^\d+$/.test(name)) continue;
      try {
        const cmdline = readFileSync(`/proc/${name}/cmdline`, "utf8");
        if (!isProjectReplProcess(readlinkSync(`/proc/${name}/cwd`), cmdline, projectDir)) continue;
        const stat = readFileSync(`/proc/${name}/stat`, "utf8");
        const tail = stat.slice(stat.lastIndexOf(")") + 2).trim().split(/\s+/);
        const group = Number(tail[2]);
        if (group === ownPid || closedPids.has(group)) continue;
        const status = readFileSync(`/proc/${name}/status`, "utf8");
        const rss = status.match(/^VmRSS:\s+(\d+)\s+kB$/m);
        const entry = byGroup.get(group) ?? { group, pids: [], rssKiB: 0 };
        entry.pids.push(Number(name));
        if (rss) entry.rssKiB += Number(rss[1]);
        byGroup.set(group, entry);
      } catch { /* process exited while /proc was being read */ }
    }
  } catch { /* /proc unavailable */ }
  return [...byGroup.values()].sort((a, b) => a.group - b.group);
}

function processGroupUsage(pid: number | undefined, projectDir: string): {
  members: number;
  rssKiB: number;
  projectReplProcesses: number;
  unexpectedProcessGroups: number[];
} {
  if (pid === undefined || process.platform !== "linux") {
    return { members: 0, rssKiB: 0, projectReplProcesses: 0, unexpectedProcessGroups: [] };
  }
  try {
    let members = 0;
    let rssKiB = 0;
    let projectReplProcesses = 0;
    const unexpectedProcessGroups = new Set<number>();
    for (const name of readdirSync("/proc")) {
      if (!/^\d+$/.test(name)) continue;
      try {
        const stat = readFileSync(`/proc/${name}/stat`, "utf8");
        const tail = stat.slice(stat.lastIndexOf(")") + 2).trim().split(/\s+/);
        const group = Number(tail[2]);
        if (group === pid) {
          members++;
          const status = readFileSync(`/proc/${name}/status`, "utf8");
          const rss = status.match(/^VmRSS:\s+(\d+)\s+kB$/m);
          if (rss) rssKiB += Number(rss[1]);
        }
        const cmdline = readFileSync(`/proc/${name}/cmdline`, "utf8");
        const cwd = readlinkSync(`/proc/${name}/cwd`);
        if (isProjectReplProcess(cwd, cmdline, projectDir)) {
          projectReplProcesses++;
          if (group !== pid) unexpectedProcessGroups.add(group);
        }
      } catch { /* process exited while /proc was being read */ }
    }
    return {
      members,
      rssKiB,
      projectReplProcesses,
      unexpectedProcessGroups: [...unexpectedProcessGroups].sort((a, b) => a - b),
    };
  } catch {
    return { members: 0, rssKiB: 0, projectReplProcesses: 0, unexpectedProcessGroups: [] };
  }
}

function downWarning(entry: RegistryEntry): string | undefined {
  if (!entry.repl || !entry.repl.alive) {
    const since = entry.downSince === undefined ? "" : ` since ${new Date(entry.downSince).toISOString()}`;
    if (entry.imports === undefined) {
      return `REPL-DOWN${since}: not initialized — call lean_repl_import first (main agent only)`;
    }
    const failures = entry.spawnFailures > 0
      ? `; ${entry.spawnFailures} consecutive initialization failure(s), last: ${entry.lastInitError ?? "unknown"}`
      : "";
    return `REPL-DOWN${since}: workers blocked, service will not auto-recover until fixed${failures}`;
  }
  if (entry.repl.alive && entry.imports !== undefined && !entry.loaded) {
    return "root environment initializing — imports not yet verified by readiness probe";
  }
  return undefined;
}

function entryStatus(entry: RegistryEntry): SharedReplStatus {
  const usage = processGroupUsage(entry.repl?.pid, entry.projectDir);
  const activeForMs = entry.activeSince === undefined ? undefined : Date.now() - entry.activeSince;
  const warnings: string[] = [];
  if (entry.pendingRequests > 1) warnings.push(`${entry.pendingRequests} REPL requests are active or queued`);
  if (activeForMs !== undefined && activeForMs >= 90_000) {
    warnings.push(`active request has run for ${Math.round(activeForMs / 1000)}s`);
  }
  const foreign = foreignReplGroups(
    entry.projectDir,
    entry.repl?.alive ? entry.repl.pid : undefined,
    entry.closedPids,
  );
  if (foreign.length > 0) {
    const detail = foreign
      .map((f) => `group ${f.group} (~${Math.round(f.rssKiB / 1024)} MB)`)
      .join("; ");
    warnings.push(
      `foreign REPL generation(s) in this project: ${detail} — spawns are refused ` +
      `(REPL-CONFLICT); use that session or free one with 'kill -9 -- -<pid>'`,
    );
  }
  if (entry.restartCount > 0) warnings.push(`${entry.restartCount} automatic REPL restart(s)`);
  const down = downWarning(entry);
  if (down) {
    if (entry.downSince === undefined && !entry.repl) entry.downSince = Date.now();
    warnings.push(down);
  }
  return {
    id: entry.repl?.id ?? "uninitialized",
    pid: entry.repl?.pid,
    references: entry.references,
    pendingRequests: entry.pendingRequests,
    activeForMs,
    totalRequests: entry.totalRequests,
    restartCount: entry.restartCount,
    lastRestartReason: entry.lastRestartReason,
    generation: entry.repl?.generation,
    restarts: { ...entry.restarts },
    recentRestarts: entry.restartLog.slice(-10),
    processGroupMembers: usage.members,
    processGroupRssKiB: usage.rssKiB,
    projectReplProcesses: usage.projectReplProcesses,
    unexpectedProcessGroups: usage.unexpectedProcessGroups,
    warnings,
    initialized: !!(entry.repl && entry.repl.alive),
    loaded: !!(entry.repl && entry.repl.alive && entry.loaded),
    imports: entry.imports,
    downSince: entry.downSince === undefined ? undefined : new Date(entry.downSince).toISOString(),
    consecutiveInitFailures: entry.spawnFailures,
    lastInitError: entry.lastInitError,
  };
}

export function getSharedReplStatus(cwd: string): SharedReplStatus | undefined {
  const entry = registry.entries.get(resolve(cwd));
  return entry === undefined ? undefined : entryStatus(entry);
}

export function acquireSharedRepl(cwd: string): SharedReplLease {
  const key = resolve(cwd);
  let entry = registry.entries.get(key);
  if (!entry) {
    entry = {
      repl: undefined,
      imports: undefined,
      loaded: false,
      downSince: undefined,
      spawnFailures: 0,
      lastInitError: undefined,
      restarts: { crash: 0, timeout: 0, import: 0 },
      restartLog: [],
      everSpawned: false,
      closedPids: new Map(),
      references: 0,
      serial: Promise.resolve(),
      pendingRequests: 0,
      activeSince: undefined,
      totalRequests: 0,
      restartCount: 0,
      lastRestartReason: undefined,
      projectDir: key,
    };
    registry.entries.set(key, entry);
  } else {
    entry.pendingRequests ??= 0;
    entry.activeSince ??= undefined;
    entry.totalRequests ??= 0;
    entry.restartCount ??= 0;
    entry.lastRestartReason ??= undefined;
    entry.projectDir ??= key;
    entry.repl ??= undefined;
    entry.imports ??= undefined;
    entry.loaded ??= false;
    entry.downSince ??= undefined;
    entry.spawnFailures ??= 0;
    entry.lastInitError ??= undefined;
    entry.restarts ??= { crash: 0, timeout: 0, import: 0 };
    entry.restartLog ??= [];
    entry.everSpawned ??= false;
    entry.closedPids ??= new Map();
  }
  entry.references++;
  const acquired = entry;
  let released = false;

  function recordRestart(reason: RestartReason, from: SharedRepl | undefined, to: SharedRepl): void {
    acquired.restarts[reason] = (acquired.restarts[reason] ?? 0) + 1;
    acquired.restartLog.push({
      reason,
      at: new Date().toISOString(),
      from: from?.id,
      to: to.id,
    });
    if (acquired.restartLog.length > 50) acquired.restartLog.splice(0, acquired.restartLog.length - 50);
    acquired.restartCount = (acquired.restartCount ?? 0) + 1;
  }

  /**
   * Spawn a REPL and verify its root environment. Caller must hold
   * `acquired.serial`. On failure the process is closed, bookkeeping records
   * the failure, and the error propagates with its probe diagnostics.
   * `ignoreCap` lets an explicit lean_repl_import retry despite consecutive
   * failures (the main agent is assumed to have fixed the cause, or is
   * deliberately probing).
   */
  function markClosed(pid: number | undefined): void {
    if (pid !== undefined) acquired.closedPids.set(pid, Date.now());
  }

  async function spawnAndInit(reason: RestartReason, ignoreCap = false): Promise<SharedRepl> {
    if (!ignoreCap && acquired.spawnFailures >= MAX_CONSECUTIVE_INIT_FAILURES) {
      throw new Error(
        `REPL-DOWN: ${acquired.spawnFailures} consecutive root initialization failures ` +
        `(last: ${acquired.lastInitError ?? "unknown"}). Automatic recovery paused — fix the cause ` +
        `(e.g. run 'cd lean && lake build' so every imported module has a .olean), then call ` +
        `lean_repl_import to reset the failure counter.`,
      );
    }
    // Singleton guard: one loaded generation holds ~7.6 GB; a second one on
    // the same host is the OOM regime that kills generations with exit(1).
    // Refuse loudly instead of silently duplicating (covers other sessions'
    // generations and leaked orphans; our own closed generations are excused
    // for a short teardown grace window).
    const foreign = foreignReplGroups(
      key,
      acquired.repl?.alive ? acquired.repl.pid : undefined,
      acquired.closedPids,
    );
    if (foreign.length > 0) {
      const parts = foreign.map((f) => `group ${f.group} (pids ${f.pids.join(",")}, ~${Math.round(f.rssKiB / 1024)} MB RSS)`);
      throw new Error(
        `REPL-CONFLICT: another process already runs a REPL generation for this project: ` +
        `${parts.join("; ")}. Only one loaded generation per project is supported ` +
        `(a loaded environment is ~7.6 GB; two on one host cause OOM kills). ` +
        `Either work in the session that owns that generation, or free it first ` +
        `with 'kill -9 -- -<pid>' and retry.`,
      );
    }
    const previous = acquired.repl;
    markClosed(previous?.pid);
    const repl = new SharedRepl(key, acquired.imports!, ++registry.generation);
    acquired.repl = repl;
    acquired.loaded = false;
    // The very first spawn of an entry initializes the service; only later
    // spawns (crash recovery, timeout, re-import) count as restarts.
    if (acquired.everSpawned) recordRestart(reason, previous, repl);
    acquired.everSpawned = true;
    try {
      await repl.rootEnvironment();
      acquired.loaded = true;
      acquired.spawnFailures = 0;
      acquired.lastInitError = undefined;
      acquired.downSince = undefined;
      return repl;
    } catch (error) {
      markClosed(repl.pid);
      await repl.close();
      if (acquired.repl === repl) acquired.repl = undefined;
      acquired.loaded = false;
      acquired.downSince ??= Date.now();
      acquired.spawnFailures++;
      const message = error instanceof Error ? error.message : String(error);
      acquired.lastInitError = message;
      acquired.lastRestartReason = message;
      throw error;
    }
  }

  async function initImports(imports: string): Promise<"initialized" | "already-running"> {
    const previous = acquired.serial;
    let release!: () => void;
    acquired.serial = new Promise<void>((resolveSerial) => { release = resolveSerial; });
    await previous;
    try {
      if (released) throw new Error("Lean REPL lease has been released");
      if (acquired.repl?.alive) {
        // Idempotent re-import: an automatic restart on request may already
        // have brought up a REPL with exactly this import block.
        if (acquired.imports !== undefined && imports.trim() === acquired.imports.trim()) {
          return "already-running";
        }
        throw new Error("REPL already initialized with a different import block — use bash to kill the process first (kill -TERM -<pid> from lean_repl_status), then call lean_repl_import again");
      }
      acquired.imports = imports;
      await spawnAndInit("import", true);
      return "initialized";
    } finally {
      release();
    }
  }

  async function request(cmd: string, env?: number, replId?: string): Promise<ReplResponse> {
    acquired.pendingRequests++;
    acquired.totalRequests++;
    const previous = acquired.serial;
    let release!: () => void;
    acquired.serial = new Promise<void>((resolveSerial) => { release = resolveSerial; });
    await previous;
    acquired.activeSince = Date.now();
    try {
      if (released) throw new Error("Lean REPL lease has been released");
      let current = acquired.repl;
      if (!current || !current.alive) {
        // Crash/dead service recovery: any requester (including read-only
        // workers, which cannot call lean_repl_import) re-spawns the REPL with
        // the last configured import block.
        if (!acquired.imports) {
          throw new Error(
            "REPL-DOWN: shared Lean REPL is not initialized — call lean_repl_import first (main agent only)",
          );
        }
        try {
          current = await spawnAndInit("crash");
          acquired.lastRestartReason = "auto-recovery: previous REPL process was dead";
        } catch (error) {
          const message = error instanceof Error ? error.message : String(error);
          throw new Error(`REPL-DOWN: automatic recovery failed: ${message}`);
        }
      }
      if (replId !== undefined && replId !== current.id) {
        throw new Error(`Stale Lean REPL handle ${replId}; current process is ${current.id}`);
      }
      if (env !== undefined && replId === undefined) {
        // Bare env handles only address the current root. Anything else would
        // silently remap onto an unrelated snapshot index of a respawned
        // process — the "successfully elaborated batch vanished" failure
        // family. Loud refusal instead (env + repl token is the safe pair).
        const root = await current.rootEnvironment();
        if (env !== root) {
          throw new Error(
            `Bare environment ${env} does not address the current root environment ${root}. ` +
            "Pass env together with the repl token, or omit env to start from the root. " +
            "After a respawn the previous generation's environments are gone by design.",
          );
        }
      }
      try {
        return await current.request(cmd, env);
      } catch (error) {
        if (acquired.repl === current && acquired.references > 0 && acquired.imports) {
          markClosed(current.pid);
          await current.close();
          if (acquired.repl === current) acquired.repl = undefined;
          acquired.loaded = false;
          const message = error instanceof Error ? error.message : String(error);
          const reason: RestartReason = /exceeded \d+ s/.test(message) ? "timeout" : "crash";
          acquired.lastRestartReason = message;
          const replacement = await spawnAndInit(reason);
          // Requests carrying stale handles cannot address the fresh root
          // safely; handle-free requests simply continue on the new root.
          if (env === undefined && replId === undefined) {
            return await replacement.request(cmd);
          }
          throw new Error(
            `${message}; Lean REPL restarted as ${replacement.id} with a verified root ` +
            `environment. Retry from the new root without stale env/repl values`,
          );
        }
        throw error;
      }
    } finally {
      acquired.activeSince = undefined;
      acquired.pendingRequests--;
      release();
    }
  }

  function status(): SharedReplStatus {
    return entryStatus(acquired);
  }

  return {
    get id() { return acquired.repl?.id ?? "uninitialized"; },
    get generation() { return acquired.repl?.generation; },
    get pid() { return acquired.repl?.pid; },
    request,
    initImports,
    status,
    async release() {
      if (released) return;
      released = true;
      acquired.references--;
      // Keep the entry (and its configured imports) so later requests — from
      // workers without lean_repl_import — can auto-recover the service.
      if (acquired.references === 0 && acquired.repl) {
        const repl = acquired.repl;
        acquired.repl = undefined;
        acquired.loaded = false;
        acquired.downSince ??= Date.now();
        markClosed(repl.pid);
        await repl.close();
      }
    },
  };
}
