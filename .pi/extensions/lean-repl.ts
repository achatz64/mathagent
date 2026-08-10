import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { Type } from "typebox";
import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";

type ReplRequest = { cmd: string; env?: number };
type ReplResponse = Record<string, unknown> & { env?: number };

class Repl {
  private readonly child: ChildProcessWithoutNullStreams;
  private buffer = "";
  private frames: string[] = [];
  private waiters: Array<{ resolve: (frame: string) => void; reject: (error: Error) => void }> = [];
  private serial: Promise<void> = Promise.resolve();
  private closed = false;

  private constructor(child: ChildProcessWithoutNullStreams) {
    this.child = child;
    child.stdout.setEncoding("utf8");
    child.stdout.on("data", (chunk: string) => this.receive(chunk));
    child.once("error", (error) => this.fail(error));
    child.once("exit", (code, signal) => {
      this.fail(new Error(`Lean REPL exited (${signal ?? code ?? "unknown"})`));
    });
  }

  static spawn(cwd: string): Repl {
    return new Repl(spawn("lake", ["exe", "repl"], {
      cwd,
      stdio: ["pipe", "pipe", "pipe"],
    }));
  }

  async request(request: ReplRequest, timeoutMs = 120_000): Promise<ReplResponse> {
    const previous = this.serial;
    let release!: () => void;
    this.serial = new Promise<void>((resolve) => { release = resolve; });
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
      // A timed-out or malformed exchange cannot safely be followed by another one.
      await this.close();
      throw error;
    } finally {
      release();
    }
  }

  async close(): Promise<void> {
    if (this.closed) return;
    this.closed = true;
    this.fail(new Error("Lean REPL closed"));
    this.child.kill("SIGTERM");
  }

  private receive(chunk: string): void {
    this.buffer += chunk;
    while (true) {
      const boundary = this.buffer.search(/\r?\n\r?\n/);
      if (boundary < 0) return;
      const frame = this.buffer.slice(0, boundary);
      const delimiter = this.buffer.match(/^([\s\S]*?)(\r?\n\r?\n)/)?.[2];
      this.buffer = this.buffer.slice(boundary + (delimiter?.length ?? 2));
      const waiter = this.waiters.shift();
      if (waiter) waiter.resolve(frame);
      else this.frames.push(frame);
    }
  }

  private nextFrame(timeoutMs: number): Promise<string> {
    if (this.frames.length > 0) return Promise.resolve(this.frames.shift()!);
    return new Promise<string>((resolve, reject) => {
      const timer = setTimeout(() => {
        const index = this.waiters.findIndex((waiter) => waiter.resolve === resolve);
        if (index >= 0) this.waiters.splice(index, 1);
        reject(new Error(`Lean REPL request exceeded ${timeoutMs / 1000}s`));
      }, timeoutMs);
      this.waiters.push({
        resolve: (frame) => { clearTimeout(timer); resolve(frame); },
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

export default function (pi: ExtensionAPI) {
  let repl: Repl | undefined;
  let mathlibEnv: Promise<number> | undefined;

  async function rootEnvironment(cwd: string): Promise<number> {
    if (!mathlibEnv) {
      mathlibEnv = (async () => {
        repl ??= Repl.spawn(cwd);
        const response = await repl.request({ cmd: "import Mathlib" });
        if (typeof response.env !== "number") throw new Error("Mathlib import returned no environment");
        return response.env;
      })();
    }
    return mathlibEnv;
  }

  pi.registerTool({
    name: "lean_repl",
    label: "Lean REPL",
    description: "Execute Lean in one persistent Mathlib REPL. Pass env from an earlier result to continue or branch; omit env to branch from the Mathlib root.",
    parameters: Type.Object({
      cmd: Type.String({ description: "Lean commands to elaborate" }),
      env: Type.Optional(Type.Integer({ description: "Environment returned by a previous lean_repl call" })),
    }),
    async execute(_toolCallId, params, _signal, _onUpdate, ctx) {
      const root = await rootEnvironment(`${ctx.cwd}/lean`);
      const response = await repl!.request({ cmd: params.cmd, env: params.env ?? root });
      return {
        content: [{ type: "text", text: JSON.stringify(response) }],
        details: response,
      };
    },
  });

  pi.on("session_shutdown", async () => {
    await repl?.close();
    repl = undefined;
    mathlibEnv = undefined;
  });
}
