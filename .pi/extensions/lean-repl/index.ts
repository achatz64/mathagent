import { Type } from "typebox";
import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { acquireSharedRepl, type SharedReplLease } from "./service.ts";

export default function (pi: ExtensionAPI) {
  let lease: SharedReplLease | undefined;

  pi.registerTool({
    name: "lean_repl_import",
    label: "Lean REPL Import",
    description: "Initialize the shared Lean REPL with an import block. Must be called before lean_repl. Main agent only: workers cannot call this. The root environment is verified by readiness probes; init fails loudly if any imported module lacks a built .olean (run 'cd lean && lake build'). Idempotent: if the live REPL already runs with exactly this import block, it succeeds as a no-op with status \"already-running\". To change imports on a live REPL, kill the process via bash (kill -TERM -<pid>) first.",
    parameters: Type.Object({
      imports: Type.String({ description: "Lean import block, e.g. 'import Mathlib\\nimport Extlib.GroupTheory.Mil21'" }),
    }),
    async execute(_toolCallId, params, _signal, _onUpdate, ctx) {
      lease ??= acquireSharedRepl(`${ctx.cwd}/lean`);
      const result = await lease.initImports(params.imports);
      const details = {
        env: 0,
        repl: lease.id,
        pid: lease.pid,
        initialized: true,
        status: result,
        imports: params.imports,
      };
      return {
        content: [{ type: "text", text: JSON.stringify(details) }],
        details,
      };
    },
  });

  pi.registerTool({
    name: "lean_repl",
    label: "Lean REPL",
    description: "Execute Lean in the project-wide shared REPL. Imports are configured by lean_repl_import; never send import commands or use #find. Pass env and repl together when retaining handles. If the service is dead, the call automatically respawns it with the last configured import block and reports the restart; retry from the new root without stale env/repl values. A REPL-DOWN error means the service could not (re)initialize — report it to the main agent.",
    promptGuidelines: [
      "Imports are configured by lean_repl_import. Never send import commands or use #find; use narrow source grep and targeted #check/#print/#synth instead. A returned env handle is durable for the lifetime of the process generation: pass env together with the repl token; a bare env (without repl) only addresses the current root. If the response's repl/generation differs from your previous call, or a failure reports an automatic restart, the environment was reset: re-elaborate the needed declarations from the root. If a failure starts with REPL-DOWN, the service could not recover: stop retrying, note it in your report as an infrastructure blocker (only the main agent can fix it via lean_repl_import or a rebuild).",
    ],
    parameters: Type.Object({
      cmd: Type.String({ description: "Lean commands to elaborate" }),
      env: Type.Optional(Type.Integer({ description: "Environment returned by an earlier lean_repl call" })),
      repl: Type.Optional(Type.String({ description: "Shared REPL generation returned by an earlier call" })),
    }),
    async execute(_toolCallId, params, _signal, _onUpdate, ctx) {
      lease ??= acquireSharedRepl(`${ctx.cwd}/lean`);
      const response = await lease.request(params.cmd, params.env, params.repl);
      const details = { ...response, repl: lease.id, generation: lease.generation, pid: lease.pid, health: lease.status() };
      return {
        content: [{ type: "text", text: JSON.stringify(details) }],
        details,
      };
    },
  });

  pi.registerTool({
    name: "lean_repl_status",
    label: "Lean REPL Status",
    description: "Inspect the shared Lean REPL generation, queue, restart count, process-group membership, and memory without submitting Lean code. loaded is true only after the root environment passed its readiness probes; a REPL-DOWN warning means workers are blocked and the main agent must intervene.",
    parameters: Type.Object({}),
    async execute(_toolCallId, _params, _signal, _onUpdate, ctx) {
      lease ??= acquireSharedRepl(`${ctx.cwd}/lean`);
      const details = lease.status();
      return {
        content: [{ type: "text", text: JSON.stringify(details) }],
        details,
      };
    },
  });

  pi.on("session_shutdown", async () => {
    await lease?.release();
    lease = undefined;
  });
}