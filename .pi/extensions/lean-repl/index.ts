import { Type } from "typebox";
import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { acquireSharedRepl, type SharedReplLease } from "./service.ts";

export default function (pi: ExtensionAPI) {
  let lease: SharedReplLease | undefined;

  pi.registerTool({
    name: "lean_repl",
    label: "Lean REPL",
    description: "Execute Lean in the project-wide shared Mathlib REPL. Pass env from an earlier result to continue or branch. Also pass repl when retaining handles across turns so stale handles are rejected.",
    parameters: Type.Object({
      cmd: Type.String({ description: "Lean commands to elaborate" }),
      env: Type.Optional(Type.Integer({ description: "Environment returned by an earlier lean_repl call" })),
      repl: Type.Optional(Type.String({ description: "Shared REPL generation returned by an earlier call" })),
    }),
    async execute(_toolCallId, params, _signal, _onUpdate, ctx) {
      lease ??= acquireSharedRepl(`${ctx.cwd}/lean`);
      const response = await lease.request(params.cmd, params.env, params.repl);
      const details = { ...response, repl: lease.id, pid: lease.pid };
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
