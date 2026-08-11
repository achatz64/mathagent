import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { Type } from "typebox";
import {
  createAgentSession,
  DefaultResourceLoader,
  getAgentDir,
  SessionManager,
  type AgentSession,
  type ExtensionAPI,
} from "@earendil-works/pi-coding-agent";

type ThinkingLevel = "off" | "minimal" | "low" | "medium" | "high" | "xhigh" | "max";
type Profile = { tools?: string[]; model?: string; thinkingLevel?: ThinkingLevel };
type Config = { maxWorkers?: number; profiles?: Record<string, Profile> };
type WorkerState = "starting" | "running" | "idle" | "done" | "failed" | "aborted";

type Worker = {
  id: string;
  task: string;
  profile: string;
  session: AgentSession;
  state: WorkerState;
  startedAt: number;
  currentTool?: string;
  latestText: string;
  finalText: string;
  error?: string;
  run: Promise<void>;
  listeners: Set<() => void>;
};

const defaultConfig: Required<Config> = {
  maxWorkers: 2,
  profiles: {
    research: { tools: ["read"] },
    lean: { tools: ["read", "grep", "lean_repl"], thinkingLevel: "high" },
  },
};

const leanWorkerProtocol = `You are a Lean proof implementer, not an API scout or theorem-search reporter.
- The mathematical source proof supplied by the main agent is authoritative and is your required construction plan. Translate it independently into Lean within the interfaces selected by the main agent.
- Searching Mathlib is only for low-level proof plumbing. Absence of a packaged theorem is not itself a blocker: prove routine and representation-independent helper lemmas yourself.
- The main agent owns architectural interface design. If the proof reaches a genuine representation choice not fixed by the task (for example module DFinsupp versus categorical biproduct, or which bundled equivalence should connect two APIs), do not silently choose a project architecture and do not merely surrender. Return an INTERFACE REQUEST containing: (1) the mathematical construction, (2) the Lean objects/APIs found, (3) the exact type-level mismatch, (4) the smallest declarations or operations the main agent must specify, and (5) all REPL-checked code completed before that boundary.
- After the main agent replies with interface signatures through a follow-up, continue the same proof in the same session. A true blocker is limited to a false/missing hypothesis, circular source argument, or persistently unavailable REPL.
- The shared lean_repl root already imports Mathlib. Never send an import command. If a request reports that the REPL automatically restarted, retry from the new root without stale env/repl values and re-elaborate the declarations needed by your branch; one terminated generation is not a blocker.
- Never use #find. Discover APIs with narrow grep in the checked-out Mathlib source, read nearby declarations, then use targeted #check/#print/#synth.
- Only claim REPL verification for dependencies from Mathlib or declarations explicitly elaborated in your REPL branch. Read project-local prerequisites and paste the minimal required declarations into the branch.
- Your final deliverable is paste-ready, REPL-checked Lean code implementing the supplied proof.`;

async function loadConfig(cwd: string): Promise<Required<Config>> {
  try {
    const parsed = JSON.parse(await readFile(join(cwd, ".pi", "subagents.json"), "utf8")) as Config;
    return {
      maxWorkers: Math.max(1, parsed.maxWorkers ?? defaultConfig.maxWorkers),
      profiles: { ...defaultConfig.profiles, ...(parsed.profiles ?? {}) },
    };
  } catch {
    return defaultConfig;
  }
}

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
  // event; emit it first so worker-owned resources (such as Lean REPLs) close.
  const runner = (session as any)._extensionRunner;
  if (runner?.emit) await runner.emit({ type: "session_shutdown", reason: "quit" });
  session.dispose();
}

function snapshot(worker: Worker) {
  return {
    id: worker.id,
    state: worker.state,
    profile: worker.profile,
    elapsedSeconds: Math.round((Date.now() - worker.startedAt) / 1000),
    currentTool: worker.currentTool,
    latestText: worker.latestText.slice(-2000),
    error: worker.error,
  };
}

export default function (pi: ExtensionAPI) {
  const workers = new Map<string, Worker>();
  const pendingNotifications = new Map<string, ReturnType<typeof setTimeout>>();
  let nextId = 1;

  // Coalesce token-level SDK events without polling; completion and tool state
  // still reach waiters promptly through pushed updates.
  const notify = (worker: Worker) => {
    if (pendingNotifications.has(worker.id)) return;
    const timer = setTimeout(() => {
      pendingNotifications.delete(worker.id);
      for (const listener of worker.listeners) listener();
    }, 100);
    pendingNotifications.set(worker.id, timer);
  };

  pi.registerTool({
    name: "subagent_spawn",
    label: "Spawn subagent",
    description: "Start an isolated helper agent. The task prompt must contain all context the helper needs.",
    parameters: Type.Object({
      task: Type.String(),
      profile: Type.Optional(Type.String({ description: "Configured profile name; defaults to research" })),
    }),
    async execute(_id, params, signal, _update, ctx) {
      const config = await loadConfig(ctx.cwd);
      if (workers.size >= config.maxWorkers) {
        throw new Error(`Worker limit reached (${config.maxWorkers}); collect or abort a worker first`);
      }

      const profileName = params.profile ?? "research";
      const profile = config.profiles[profileName];
      if (!profile) throw new Error(`Unknown profile ${profileName}`);

      const loader = new DefaultResourceLoader({
        cwd: ctx.cwd,
        agentDir: getAgentDir(),
        appendSystemPrompt: profileName === "lean" ? [leanWorkerProtocol] : [],
      });
      await loader.reload();
      const model = profile.model
        ? ctx.modelRegistry.find(...(profile.model.includes("/")
          ? profile.model.split("/", 2) as [string, string]
          : [ctx.model?.provider ?? "", profile.model] as [string, string]))
        : ctx.model;
      if (!model) throw new Error(`Model unavailable: ${profile.model ?? "current model"}`);

      const { session } = await createAgentSession({
        cwd: ctx.cwd,
        model,
        thinkingLevel: profile.thinkingLevel ?? ctx.thinkingLevel,
        tools: profile.tools ?? ["read"],
        resourceLoader: loader,
        sessionManager: SessionManager.inMemory(ctx.cwd),
      });

      const worker = {
        id: `w${nextId++}`,
        task: params.task,
        profile: profileName,
        session,
        state: "starting" as WorkerState,
        startedAt: Date.now(),
        latestText: "",
        finalText: "",
        listeners: new Set<() => void>(),
        run: Promise.resolve(),
      } satisfies Worker;
      workers.set(worker.id, worker);

      session.subscribe((event: any) => {
        if (event.type === "agent_start") worker.state = "running";
        if (event.type === "tool_execution_start") worker.currentTool = event.toolName;
        if (event.type === "tool_execution_end") worker.currentTool = undefined;
        if (event.type === "message_update" && event.assistantMessageEvent?.type === "text_delta") {
          worker.latestText += event.assistantMessageEvent.delta;
        }
        notify(worker);
      });

      worker.run = session.prompt(params.task).then(() => {
        worker.finalText = assistantText(session.messages);
        worker.latestText = worker.finalText;
        worker.state = "done";
      }).catch((error) => {
        worker.error = error instanceof Error ? error.message : String(error);
        worker.state = signal?.aborted ? "aborted" : "failed";
      }).finally(() => notify(worker));

      return { content: [{ type: "text", text: `Started ${worker.id}` }], details: snapshot(worker) };
    },
  });

  pi.registerTool({
    name: "subagent_send",
    label: "Send to subagent",
    description: "Send steering or follow-up context to a running helper agent.",
    parameters: Type.Object({ id: Type.String(), message: Type.String(), followUp: Type.Optional(Type.Boolean()) }),
    async execute(_id, params) {
      const worker = workers.get(params.id);
      if (!worker) throw new Error(`Unknown worker ${params.id}`);
      if (worker.session.isStreaming) {
        if (params.followUp) await worker.session.followUp(params.message);
        else await worker.session.steer(params.message);
      } else {
        worker.state = "running";
        worker.run = worker.session.prompt(params.message).then(() => {
          worker.finalText = assistantText(worker.session.messages);
          worker.latestText = worker.finalText;
          worker.state = "done";
        }).catch((error) => {
          worker.error = error instanceof Error ? error.message : String(error);
          worker.state = "failed";
        }).finally(() => notify(worker));
      }
      return { content: [{ type: "text", text: `Sent to ${worker.id}` }], details: snapshot(worker) };
    },
  });

  pi.registerTool({
    name: "subagent_status",
    label: "Subagent status",
    description: "Inspect live helper-agent state without shell polling.",
    parameters: Type.Object({ id: Type.Optional(Type.String()) }),
    async execute(_id, params) {
      const selected = params.id ? [workers.get(params.id)].filter(Boolean) as Worker[] : [...workers.values()];
      return { content: [{ type: "text", text: JSON.stringify(selected.map(snapshot), null, 2) }], details: selected.map(snapshot) };
    },
  });

  pi.registerTool({
    name: "subagent_wait",
    label: "Wait for subagent",
    description: "Wait for a helper to finish; progress is pushed through tool updates.",
    parameters: Type.Object({ id: Type.String() }),
    async execute(_id, params, signal, onUpdate) {
      const worker = workers.get(params.id);
      if (!worker) throw new Error(`Unknown worker ${params.id}`);
      const update = () => onUpdate?.({ content: [{ type: "text", text: JSON.stringify(snapshot(worker), null, 2) }], details: snapshot(worker) });
      worker.listeners.add(update);
      const abort = () => worker.session.abort();
      signal?.addEventListener("abort", abort, { once: true });
      try { await worker.run; } finally {
        worker.listeners.delete(update);
        signal?.removeEventListener("abort", abort);
      }
      if (worker.state === "failed") throw new Error(worker.error ?? "Subagent failed");
      return { content: [{ type: "text", text: worker.finalText || worker.latestText || "(no output)" }], details: snapshot(worker) };
    },
  });

  pi.registerTool({
    name: "subagent_abort",
    label: "Abort subagent",
    description: "Abort and dispose a helper agent.",
    parameters: Type.Object({ id: Type.String() }),
    async execute(_id, params) {
      const worker = workers.get(params.id);
      if (!worker) throw new Error(`Unknown worker ${params.id}`);
      await worker.session.abort();
      worker.state = "aborted";
      await disposeSession(worker.session);
      workers.delete(worker.id);
      notify(worker);
      return { content: [{ type: "text", text: `Aborted ${worker.id}` }], details: snapshot(worker) };
    },
  });

  pi.registerTool({
    name: "subagent_collect",
    label: "Collect subagent",
    description: "Return a completed helper's result and optionally dispose it.",
    parameters: Type.Object({ id: Type.String(), dispose: Type.Optional(Type.Boolean({ default: true })) }),
    async execute(_id, params) {
      const worker = workers.get(params.id);
      if (!worker) throw new Error(`Unknown worker ${params.id}`);
      if (worker.state === "running" || worker.state === "starting") throw new Error(`${worker.id} is still running`);
      const text = worker.finalText || worker.latestText || worker.error || "(no output)";
      if (params.dispose ?? true) {
        await disposeSession(worker.session);
        workers.delete(worker.id);
      }
      return { content: [{ type: "text", text }], details: snapshot(worker) };
    },
  });

  pi.on("session_shutdown", async () => {
    await Promise.all([...workers.values()].map(async (worker) => {
      await worker.session.abort().catch(() => undefined);
      await disposeSession(worker.session);
    }));
    for (const timer of pendingNotifications.values()) clearTimeout(timer);
    pendingNotifications.clear();
    workers.clear();
  });
}
