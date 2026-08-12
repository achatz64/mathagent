import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { existsSync, readdirSync, readFileSync, readlinkSync } from "node:fs";
import { join, resolve } from "node:path";

type ReplRequest = { cmd: string; env?: number };
export type ReplResponse = Record<string, unknown> & { env?: number };

type Waiter = { resolve: (frame: string) => void; reject: (error: Error) => void };

class SharedRepl {
  readonly id: string;
  readonly pid: number | undefined;
  private readonly child: ChildProcessWithoutNullStreams;
  private readonly exited: Promise<void>;
  private buffer = "";
  private frames: string[] = [];
  private waiters: Waiter[] = [];
  private serial: Promise<void> = Promise.resolve();
  private root: Promise<number> | undefined;
  private closed = false;

  constructor(cwd: string, generation: number) {
    const binary = join(cwd, ".lake", "packages", "repl", ".lake", "build", "bin", "repl");
    // Give the launcher and REPL their own process group. Killing only `lake`
    // leaves its Lean child orphaned after a timeout, so the whole group must
    // be terminated when framing is lost or a generation is replaced.
    const options = { cwd, stdio: ["pipe", "pipe", "pipe"] as const, detached: true };
    this.child = existsSync(binary)
      ? spawn("lake", ["env", binary], options)
      : spawn("lake", ["exe", "repl"], options);
    this.pid = this.child.pid;
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

  rootEnvironment(): Promise<number> {
    this.root ??= this.requestRaw({ cmd: "import Mathlib" }).then((response) => {
      if (typeof response.env !== "number") throw new Error("Mathlib import returned no environment");
      return response.env;
    });
    return this.root;
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
      // Once framing is uncertain, no client may safely continue on this process.
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
  processGroupMembers: number;
  processGroupRssKiB: number;
  projectReplProcesses: number;
  unexpectedProcessGroups: number[];
  warnings: string[];
};

type RegistryEntry = {
  repl: SharedRepl;
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
  readonly pid: number | undefined;
  request(cmd: string, env?: number, replId?: string): Promise<ReplResponse>;
  status(): SharedReplStatus;
  release(): Promise<void>;
};

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
        if (cwd === projectDir && cmdline.includes("/.lake/packages/repl/.lake/build/bin/repl")) {
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

function entryStatus(entry: RegistryEntry): SharedReplStatus {
  const usage = processGroupUsage(entry.repl.pid, entry.projectDir);
  const activeForMs = entry.activeSince === undefined ? undefined : Date.now() - entry.activeSince;
  const warnings: string[] = [];
  if (entry.pendingRequests > 1) warnings.push(`${entry.pendingRequests} REPL requests are active or queued`);
  if (activeForMs !== undefined && activeForMs >= 90_000) {
    warnings.push(`active request has run for ${Math.round(activeForMs / 1000)}s`);
  }
  if (usage.unexpectedProcessGroups.length > 0) {
    warnings.push(`unexpected project REPL process groups: ${usage.unexpectedProcessGroups.join(", ")}`);
  }
  if (entry.restartCount > 0) warnings.push(`${entry.restartCount} automatic REPL restart(s)`);
  return {
    id: entry.repl.id,
    pid: entry.repl.pid,
    references: entry.references,
    pendingRequests: entry.pendingRequests,
    activeForMs,
    totalRequests: entry.totalRequests,
    restartCount: entry.restartCount,
    lastRestartReason: entry.lastRestartReason,
    processGroupMembers: usage.members,
    processGroupRssKiB: usage.rssKiB,
    projectReplProcesses: usage.projectReplProcesses,
    unexpectedProcessGroups: usage.unexpectedProcessGroups,
    warnings,
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
      repl: new SharedRepl(key, ++registry.generation),
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
    // Extension hot reloads preserve the process-wide registry. Initialize any
    // monitoring fields added by a newer service version.
    entry.pendingRequests ??= 0;
    entry.activeSince ??= undefined;
    entry.totalRequests ??= 0;
    entry.restartCount ??= 0;
    entry.lastRestartReason ??= undefined;
    entry.projectDir ??= key;
  }
  entry.references++;
  const acquired = entry;
  let released = false;

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
      const current = acquired.repl;
      if (replId !== undefined && replId !== current.id) {
        throw new Error(`Stale Lean REPL handle ${replId}; current process is ${current.id}`);
      }
      try {
        return await current.request(cmd, env);
      } catch (error) {
        if (acquired.repl === current && acquired.references > 0) {
          await current.close();
          acquired.repl = new SharedRepl(key, ++registry.generation);
          const message = error instanceof Error ? error.message : String(error);
          acquired.restartCount++;
          acquired.lastRestartReason = message;
          throw new Error(
            `${message}; Lean REPL restarted as ${acquired.repl.id}. Retry from the new root`,
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
    get id() { return acquired.repl.id; },
    get pid() { return acquired.repl.pid; },
    request,
    status,
    async release() {
      if (released) return;
      released = true;
      acquired.references--;
      if (acquired.references === 0 && registry.entries.get(key) === acquired) {
        registry.entries.delete(key);
        await acquired.repl.close();
      }
    },
  };
}
