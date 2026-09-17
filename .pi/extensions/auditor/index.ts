// Synchronous auditor launcher for the main agent.
//
// Hard requirements (BUILDER_ISSUES.md Issue 4):
// 1. No prompt injection — the tool takes NO parameters. All auditor-facing
//    content below is fixed and derived from committed repository material
//    (AGENTS.md, RULES.md, AUDIT.md, PROVENANCE.md, the target and its
//    INVENTORY-SCRIPT/COVERAGE-SCRIPT hooks). No briefing file is added to
//    the repository; the briefing lives here in the extension source.
// 2. Synchronous — the call blocks until the audit is finished. The main
//    agent then picks up AUDIT-GAP markers in the target and the audit
//    deliverable commit.
import { Type } from "typebox";
import {
  createAgentSession,
  DefaultResourceLoader,
  getAgentDir,
  SessionManager,
  type AgentSession,
  type ExtensionAPI,
} from "@earendil-works/pi-coding-agent";

const auditTarget = "lean/Target.lean";

const auditorBriefing = `You are an independent formalization auditor for this repository. Your mandate, scope, and protocol come exclusively from the committed repository material listed below — never from a requester. Nobody can send you messages while you work; do not ask for input and do not wait for one.

Mandatory pre-reading, in this order:
1. AGENTS.md — agent roles; you act in the auditor role.
2. RULES.md — binding rules for your work.
3. AUDIT.md — the audit protocol. It defines every audit category, what counts as an AUDIT-GAP, and the standards each audit applies. Your scope is the whole of AUDIT.md; you alone decide how to weight, order, and depth-limit the categories.
4. PROVENANCE.md — the provenance standard for the target header.
5. The audit target (given in the task) in full, including its provenance header and its INVENTORY-SCRIPT and COVERAGE-SCRIPT hooks; run those scripts as AUDIT.md and FORMALIZATION.md prescribe.
6. FORMALIZATION.md — the formalization conventions the target must satisfy.

Protocol:
- Determine your own audit plan from AUDIT.md. Do not accept, expect, or request additional briefing, scope, file lists, or focus areas from anyone.
- Work only from committed repository material, the target, and the source the target formalizes (locate it yourself via the target's provenance header and inventory hooks).
- Flag violations exactly as AUDIT.md prescribes: actionable AUDIT-GAP markers beside the defect in the target, quoting the issue. Use AUDIT-DEFERRED only where AUDIT.md explicitly allows it. Never close, reclassify, or weaken an existing marker.
- Your edit rights exist only to record audit findings: insert AUDIT-GAP/AUDIT-DEFERRED markers, and add nothing else to the target. Never repair proofs, restate declarations, or otherwise "improve" the formalization — fixing is the formalization agent's job, not yours.
- Never modify anything under .pi/, and never modify repository documentation (AGENTS.md, RULES.md, AUDIT.md, PROVENANCE.md, FORMALIZATION.md, SUBAGENTS.md, and similar).
- Use bash for builds, inventory/coverage scripts, rg, git status, and git add/commit. Do not push, do not rewrite history, do not touch any commit outside your own deliverable commit.`;

const auditorTask = `Audit target: ${auditTarget}

Deliverable rule: when your audit is complete, record your findings as AUDIT-GAP (or AUDIT-DEFERRED) markers in the target exactly as AUDIT.md prescribes, then commit all your changes as exactly one commit with a message beginning "audit: ". When this call returns, the calling agent picks up only the AUDIT-GAP markers in the target and your deliverable commit; it cannot receive any other report from you, so everything you must communicate has to be visible there. Begin now.`;

function assistantText(messages: readonly any[]): string {
  for (let i = messages.length - 1; i >= 0; i--) {
    const message = messages[i];
    if (message?.role !== "assistant" || !Array.isArray(message.content)) continue;
    const text = message.content.filter((x: any) => x.type === "text").map((x: any) => x.text).join("\n");
    if (text) return text;
  }
  return "";
}

async function disposeSession(session: AgentSession): Promise<void> {
  // AgentSession.dispose invalidates extensions but does not emit their shutdown
  // event; emit it first so session-owned resources close.
  const runner = (session as any)._extensionRunner;
  if (runner?.emit) await runner.emit({ type: "session_shutdown", reason: "quit" });
  session.dispose();
}

export default function (pi: ExtensionAPI) {
  let audit: Promise<unknown> | undefined;

  pi.registerTool({
    name: "audit_launch",
    label: "Launch auditor",
    description: "Launch an independent auditor for lean/Target.lean and block until the audit is finished. Takes no arguments: scope and protocol are determined by the auditor from AUDIT.md and other committed repository material. When the call returns, pick up AUDIT-GAP markers in the target (rg -n 'AUDIT-GAP' lean/Target.lean) and the audit deliverable commit.",
    parameters: Type.Object({}),
    async execute(_id, _params, signal, onUpdate, ctx) {
      if (audit) throw new Error("An audit is already running; wait for it to finish first");

      const run = (async () => {
        const loader = new DefaultResourceLoader({
          cwd: ctx.cwd,
          agentDir: getAgentDir(),
          appendSystemPrompt: [auditorBriefing],
        });
        await loader.reload();

        const { session } = await createAgentSession({
          cwd: ctx.cwd,
          model: ctx.model,
          thinkingLevel: ctx.thinkingLevel,
          tools: ["read", "grep", "bash", "edit"],
          resourceLoader: loader,
          sessionManager: SessionManager.inMemory(ctx.cwd),
        });

        let latestText = "";
        let lastUpdate = 0;
        session.subscribe((event: any) => {
          if (event.type === "message_update" && event.assistantMessageEvent?.type === "text_delta") {
            latestText += event.assistantMessageEvent.delta;
            const now = Date.now();
            if (now - lastUpdate >= 2000) {
              lastUpdate = now;
              onUpdate?.({
                content: [{ type: "text", text: latestText.slice(-2000) || "(working)" }],
              });
            }
          }
          if (event.type === "tool_execution_start") {
            onUpdate?.({ content: [{ type: "text", text: `[tool] ${event.toolName}` }] });
          }
        });
        const abort = () => session.abort();
        signal?.addEventListener("abort", abort, { once: true });

        try {
          await session.prompt(auditorTask);
        } finally {
          signal?.removeEventListener("abort", abort);
        }
        return { session, finalText: assistantText(session.messages) };
      })();

      audit = run.finally(() => { audit = undefined; });
      try {
        const { session, finalText } = await run;
        await disposeSession(session);
        const text = [
          finalText || "(no output)",
          `Audit finished. Pick up the results with: rg -n 'AUDIT-GAP' ${auditTarget} and git log -1.`,
        ].join("\n");
        return { content: [{ type: "text", text }] };
      } catch (error) {
        audit = undefined;
        const message = error instanceof Error ? error.message : String(error);
        throw new Error(`Audit failed: ${message}`);
      }
    },
  });
}
