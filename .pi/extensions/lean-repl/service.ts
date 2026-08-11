import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { existsSync } from "node:fs";
import { join, resolve } from "node:path";

type ReplRequest = { cmd: string; env?: number };
export type ReplResponse = Record<string, unknown> & { env?: number };

type Waiter = { resolve: (frame: string) => void; reject: (error: Error) => void };

class SharedRepl {
  readonly id: string;
  readonly pid: number | undefined;
  private readonly child: ChildProcessWithoutNullStreams;
  private buffer = "";
  private frames: string[] = [];
  private waiters: Waiter[] = [];
  private serial: Promise<void> = Promise.resolve();
  private root: Promise<number> | undefined;
  private closed = false;

  constructor(cwd: string, generation: number) {
    const binary = join(cwd, ".lake", "packages", "repl", ".lake", "build", "bin", "repl");
    this.child = existsSync(binary)
      ? spawn("lake", ["env", binary], { cwd, stdio: ["pipe", "pipe", "pipe"] })
      : spawn("lake", ["exe", "repl"], { cwd, stdio: ["pipe", "pipe", "pipe"] });
    this.pid = this.child.pid;
    this.id = `${generation}:${this.pid ?? "pending"}`;
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
    this.child.kill("SIGTERM");
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

type RegistryEntry = {
  repl: SharedRepl;
  references: number;
  serial: Promise<void>;
};
type Registry = { generation: number; entries: Map<string, RegistryEntry> };
const registryKey = Symbol.for("mathagent.shared-lean-repl.registry");
const globals = globalThis as typeof globalThis & { [registryKey]?: Registry };
const registry = globals[registryKey] ??= { generation: 0, entries: new Map() };

export type SharedReplLease = {
  readonly id: string;
  readonly pid: number | undefined;
  request(cmd: string, env?: number, replId?: string): Promise<ReplResponse>;
  release(): Promise<void>;
};

export function acquireSharedRepl(cwd: string): SharedReplLease {
  const key = resolve(cwd);
  let entry = registry.entries.get(key);
  if (!entry) {
    entry = {
      repl: new SharedRepl(key, ++registry.generation),
      references: 0,
      serial: Promise.resolve(),
    };
    registry.entries.set(key, entry);
  }
  entry.references++;
  const acquired = entry;
  let released = false;

  async function request(cmd: string, env?: number, replId?: string): Promise<ReplResponse> {
    const previous = acquired.serial;
    let release!: () => void;
    acquired.serial = new Promise<void>((resolveSerial) => { release = resolveSerial; });
    await previous;
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
          throw new Error(
            `${message}; Lean REPL restarted as ${acquired.repl.id}. Retry from the new root`,
          );
        }
        throw error;
      }
    } finally {
      release();
    }
  }

  return {
    get id() { return acquired.repl.id; },
    get pid() { return acquired.repl.pid; },
    request,
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
