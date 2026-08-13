import { Type } from "typebox";
import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { acquireSharedRepl, type SharedReplLease } from "./service.ts";

export default function (pi: ExtensionAPI) {
  let lease: SharedReplLease | undefined;

  pi.registerTool({
    name: "lean_repl_import",
    label: "Lean REPL Import",
    description: "Initialize or restart the shared Lean REPL with an import block. Must be called before lean_repl. Call again to restart with new imports (e.g. when Extlib changes).",
    parameters: Type.Object({
      imports: Type.String({ description: "Lean import block, e.g. 'import Mathlib\\nimport Extlib.GroupTheory.Mil21'" }),
    }),
    async execute(_toolCallId, params, _signal, _onUpdate, ctx) {
      lease ??= acquireSharedRepl(`${ctx.cwd}/lean`);
      await lease.initImports(params.imports);
      const details = {
        env: 0,
        repl: lease.id,
        pid: lease.pid,
        initialized: true,
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
    description: "Execute Lean in the project-wide shared REPL. Imports are configured by lean_repl_import; never send import commands or use #find. Pass env and repl together when retaining handles. After an automatic restart, retry from the new root without stale env/repl values.",
    promptGuidelines: [
      "Imports are configured by lean_repl_import. Never send import commands or use #find; use narrow source grep and targeted #check/#print/#synth instead. If a failure reports an automatic restart, retry from the new root and re-elaborate needed declarations.",
    ],
    parameters: Type.Object({
      cmd: Type.String({ description: "Lean commands to elaborate" }),
      env: Type.Optional(Type.Integer({ description: "Environment returned by an earlier lean_repl call" })),
      repl: Type.Optional(Type.String({ description: "Shared REPL generation returned by an earlier call" })),
    }),
    async execute(_toolCallId, params, _signal, _onUpdate, ctx) {
      lease ??= acquireSharedRepl(`${ctx.cwd}/lean`);
      const response = await lease.request(params.cmd, params.env, params.repl);
      const details = { ...response, repl: lease.id, pid: lease.pid, health: lease.status() };
      return {
        content: [{ type: "text", text: JSON.stringify(details) }],
        details,
      };
    },
  });

  pi.registerTool({
    name: "lean_repl_status",
    label: "Lean REPL Status",
    description: "Inspect the shared Lean REPL generation, queue, restart count, process-group membership, and memory without submitting Lean code.",
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