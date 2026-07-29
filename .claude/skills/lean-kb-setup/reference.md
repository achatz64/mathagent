# Reference: components, costs, limits

Figures below are measured or taken from upstream measurements, not estimates,
and drive the thresholds in `scripts/common.sh`.

## Component inventory

| # | Component | Source | Installed by |
|---|---|---|---|
| 1 | `uv` | astral.sh install script, or Homebrew | `install.sh --only uv` |
| 2 | `elan` | elan.lean-lang.org install script | `install.sh --only elan` |
| 3 | `ripgrep` | system package manager (**needs root**) | `install.sh --only ripgrep --allow-sudo` |
| 4 | Mathlib | `leanprover-community/mathlib4` @ tag matching `lean-toolchain` | `install.sh --only mathlib` |
| 5 | Lean REPL | `leanprover-community/repl` @ same tag | `install.sh --only repl` |
| 6 | `lean-lsp-mcp` | PyPI, pinned in `common.sh` | `install.sh --only leanlsp` |
| 7 | local Loogle | `nomeata/loogle`, cloned and built by the server itself | `install.sh --only loogle` |
| 8 | `lean-explore[local]` | PyPI, pinned in `common.sh` | `install.sh --only leanexplore` |
| 9 | LeanExplore data | Cloudflare R2, `lean-explore data fetch` | same stage |
| 10 | Qwen3 embedding + reranker | HuggingFace, on first search | same stage |

## Disk

| Location | Contents | Size |
|---|---|---|
| `~/.elan/toolchains` | **one Lean toolchain per pinned version** | **~2.8 GiB each** |
| `<project>/.lake` | Mathlib + deps + repl (estimate) | ~9 GiB |
| `~/.cache/lean-lsp-mcp/loogle` | loogle checkout, binary, Mathlib index | ~2 GiB |
| `~/.lean_explore/cache/<version>` | `lean_explore.db` 2.18 GB, `informalization_faiss.index` 1.68 GB, id maps | 3.86 GiB |
| `~/.cache/huggingface` | `Qwen3-Embedding-0.6B` 1.19 GB + `Qwen3-Reranker-0.6B` 1.19 GB | ~2.5 GiB |
| uv tool venvs | both servers; torch dominates | ~1.5 GiB CPU-only, ~3.5 GiB with CUDA |

Budget ~25 GiB total, and note the toolchain cost is *per pinned Lean version* —
projects on different toolchains do not share one.

## Memory

| Operation | Peak RSS |
|---|---|
| LSP tools over a built Mathlib | ~2–4 GiB |
| **local Loogle, first index** | **~13 GiB** |
| local Loogle, warm load | ~7 GiB |
| LeanExplore local search | ~4–6 GiB (1.68 GB FAISS index plus two 0.6B models) |

The Loogle index is the binding constraint for the whole stack. Under ~14 GiB it
OOMs, and `lean_loogle` falls back to the remote API *silently* — which is why
`install.sh` builds the index in the foreground and `verify.sh` checks for the
`.idx` file rather than trusting a successful query.

**There is no fallback**, at three layers:

1. **Install time.** No index after the attempt ⇒ the loogle stage stops the
   install. Preflight FAILs below ~14 GiB rather than letting a default run get
   that far.
2. **Registration.** `stage_register` refuses to register `lean-lsp` without
   `--loogle-local` unless you passed `--skip loogle`. Registering a working
   server pointed at the remote API is exactly the accident being prevented.
3. **Runtime.** `lean_loogle` catches *any* local exception, logs "falling back
   to remote", and answers from `loogle.lean-lang.org`. There is no strict
   switch upstream — but `LOOGLE_URL` is its documented knob for redirecting the
   remote backend, so registration pins it to `http://127.0.0.1:1`. The
   fall-through then raises a connection error instead of quietly succeeding.

`verify.sh` checks all four: the index file, a live query run with the dead
endpoint in place (so an index that exists but does not *load* cannot pass), the
registered `--loogle-local` flag, and that `LOOGLE_URL` is the exact dead
endpoint — a reachable one is a FAIL, since warnings do not affect the exit
status. `--skip loogle` is the single deliberate route to the remote API, and it
suppresses every one of these checks together.

The last two are read from `introspect.py mcp-registered --env-key
--has-arg=…`, which answers with `env_value` and an exact `has_arg` membership
test. The `args`/`env` fields it also returns are flattened with spaces and `=`
**for printing only**. Matching against those is not the exact check it looks
like — with the pin at `http://127.0.0.1:1`, all three of these satisfy a
substring test while leaving the fallback wide open:

| Registration | Why the substring test passes | What it actually is |
| --- | --- | --- |
| `NOTE=LOOGLE_URL=http://127.0.0.1:1-suffix` | the pin is a substring of another variable's value | `LOOGLE_URL` unset |
| `LOOGLE_URL=http://127.0.0.1:10` | the pin is a prefix of the port | a different endpoint |
| `--loogle-local=false` | contains `--loogle-local` | the flag disabled |

### Rolling back a registration

Rollback works on `mcpServers.<name>` at one scope, never on whole files.
Whole-file restore could not undo anything in `~/.claude.json` without also
reverting unrelated Claude Code state, so a failed `add` there stayed live — and
the next run's probe would read that skill-created entry back as somebody
else's `preexisting`. It also clobbered concurrent edits.

`introspect.py mcp-entry get|restore` snapshots and reinstates just that
subtree, deleting the key when there was nothing before, and removing the file
only when it did not exist beforehand and nothing else ended up in it. The
read-modify-write window shrinks from "snapshot until failure" to a few
milliseconds inside one process.

**A config that cannot be read is not an empty config.** A malformed container —
`mcpServers` holding a number, `projects` holding a string, either of them
holding `null` — makes both `mcp-entry get` and `mcp-registered` answer
*unknown* (`readable: false`, `registered: null`), never *absent*. The `null`
case needs a membership test rather than `.get()`, which cannot tell a missing
key from a key set to null; without that the four shapes `mcpServers: null`,
`projects: null`, `projects.<root>: null` and `projects.<root>.mcpServers: null`
all read as an empty config, and a create would overwrite the very value that
made it unreadable. Reporting any of this as absent is the dangerous
direction: the installer would see "nothing registered", write into it, and hold
a snapshot saying the same thing. So `stage_register` reads `readable` before
the first `claude mcp add` and **refuses to register at all** when the snapshot
is unusable — the one case where a failed add could not be undone. It records
nothing in provenance (an unknown is not evidence either way) and marks the
stage incomplete, so the run exits non-zero. Fix the config by hand and re-run
`--only register`.

**When a rollback itself fails, the in-flight marker stays.** Re-probing the
config is only legitimate once it is back to what was snapshotted. If the
restore failed — readable but no longer writable, say — the entry sitting there
may be the half-written one this run produced, and observing it would record
`preexisting`: a settled action that outranks `installing`/`replacing` in the
merge and carries `origin: user`, reclassifying the skill's own mutation as
something that predated it. So the failure path records nothing new, and says
the config may still hold a partial registration rather than claiming a restore
that did not happen.

### What a correct registration looks like

`verify.sh` validates the whole entry for **both** servers before printing PASS,
because a malformed or misdirected registration starts nothing and a check that
announces "registered" first exits 0 on it:

| | `lean-lsp` | `lean-explore` |
| --- | --- | --- |
| entry is a JSON object | required | required |
| `command` basename | `lean-lsp-mcp` | `lean-explore` |
| required args | `--repl` | `mcp`, `serve` |
| exact option value | `--lean-project-path` = the project being verified | `--backend` = `local` |
| conditional | `--loogle-local` and `LOOGLE_URL` unless `--skip loogle` | — |

The project path is compared, not merely found: a server pointed at a different
Lean project answers every query happily, about the wrong code. `--backend`
likewise — the same binary without it is the hosted API, which needs
`LEANEXPLORE_API_KEY` and answers from the network.

### What the manifest will *not* claim

Version keys are owned by stages that ran **to completion**. A stage that was
not selected, or that failed, leaves its keys untouched — they are preserved,
never seeded. `install.sh` emits its version constants on every run regardless
of which stages ran, so seeding would have `--only register` assert that
lean-lsp-mcp and lean-explore are installed when neither stage was selected.

Running local Loogle and LeanExplore concurrently wants ~13 GiB together even
after both are warm.

### Parallel Lake workers

Lake defaults to one worker per core. That is harmless while `lake exe cache
get` hits — unpacking oleans is I/O — but on a miss Mathlib compiles from
source and every worker is a full `lean` process holding its imports resident.
Sixteen cores against 8 GiB is an OOM kill partway through a multi-hour build,
reported as an opaque Lake failure.

`install.sh` therefore caps `lake build` at
`min(cores, (RAM − 2 GiB) / 2 GiB)`, never below 1:

| RAM | cores | `-j` |
|---|---|---|
| 4 GiB | 8 | 1 |
| 7.4 GiB | 16 | 2 |
| 16 GiB | 8 | 7 |
| 32 GiB | 16 | 15 |

It is a floor on safety, not a tuning parameter — `--lake-jobs N` or
`LEAN_KB_LAKE_JOBS=N` overrides it outright, and the effective value is recorded
in the manifest as `lake_jobs`.

## Platform limits

- **Local Loogle is Unix-only.** Linux, macOS, WSL2. Native Windows must use the
  remote API.
- **`LEAN_REPL_MEM_MB` is enforced on Linux/macOS only.**
- **WSL2 defaults to ~50% of host RAM.** On a 16 GB host that is ~7.5 GiB — below
  the Loogle indexing threshold. Raise it in `%USERPROFILE%\.wslconfig`:

  ```ini
  [wsl2]
  memory=14GB
  swap=8GB
  ```

  then `wsl --shutdown` from Windows. On a 16 GB host this leaves Windows ~2 GB;
  the alternative is `install.sh --skip loogle` and living with the remote API.
  This is a host-level change with a reboot, so the skill reports it and lets the
  user decide.
- **Do not build on `/mnt/c` under WSL.** Windows drives are mounted over 9p;
  Lean's many small files make builds 5–10x slower, and `lean-lsp-mcp` hard-codes
  a 900 s Loogle build timeout and a 300 s index-readiness timeout that a 9p build
  will blow through. Keep the Lean project on the WSL ext4 filesystem.
- **Linux torch pulls CUDA wheels, but no component needs a GPU.** `lean-explore[local]`
  depends on torch, whose default Linux x86_64 install adds four `nvidia-cu13`
  wheels (cudnn, nccl, cusparselt, nvshmem — ~0.81 GB compressed, ~2 GiB unpacked)
  on top of torch's own 0.53 GB wheel. That is *packaging*, not a requirement:
  torch runs on CPU regardless, and `lean-explore` pins `faiss-cpu`, so vector
  search never touches a GPU. `install.sh` sets `UV_TORCH_BACKEND=cpu` when no
  `nvidia-smi` is present purely to save the disk, falling back to the default
  wheel if uv is too old to know the flag.

  A GPU, if present, only accelerates the two Qwen3 0.6B models (~2.5 GiB VRAM
  for both at bf16). Lean, Mathlib, Loogle, and ripgrep are CPU-only throughout.

## Local vs remote tool coverage

Local after a full install: all 16 LSP tools (`lean_goal`, `lean_diagnostic_messages`,
`lean_hover_info`, `lean_completions`, `lean_run_code`, `lean_multi_attempt`,
`lean_verify`, `lean_profile_proof`, …), `lean_local_search`, `lean_build`,
`lean_loogle`, and all 8 LeanExplore tools (`search`, `search_summary`,
`get_source_code`, `get_source_link`, `get_docstring`, `get_description`,
`get_module`, `get_dependencies`).

Remote-only, no local mode: `lean_leansearch` (leansearch.net),
`lean_leanfinder` (HuggingFace). Remote by default but self-hostable:
`lean_state_search` (`LEAN_STATE_SEARCH_URL`), `lean_hammer_premise` (`LEAN_HAMMER_URL`).

## How local Loogle actually works

Worth knowing, because the failure modes are unintuitive:

1. The server clones `nomeata/loogle` at a pinned revision into
   `~/.cache/lean-lsp-mcp/loogle/repo-<ref>-<toolchain-hash>`.
2. It builds with `ELAN_TOOLCHAIN` forced to **your project's** toolchain and
   `LAKE_ARTIFACT_CACHE=false`. At the pinned revision loogle's `lake-manifest.json`
   has no packages, so this builds only loogle — it does not build a second Mathlib.
3. It runs the binary through `lake env` with the **project** as cwd, so the
   Mathlib being indexed is your project's. The index lands in
   `~/.cache/lean-lsp-mcp/loogle/index/mathlib-<project-hash>.idx`.
4. Loogle hashes `.olean` dependencies, so changing your project's Mathlib
   invalidates and rebuilds the index automatically.

Consequences: the index is per-(project, toolchain) — two projects on different
toolchains each pay the ~13 GiB indexing cost — and a project without Mathlib has
nothing to index, which is why `install.sh` stops rather than pretending the
stage succeeded.

## LeanExplore data toolchains

`lean-explore data fetch` reads a manifest from Cloudflare R2 and installs the
`default_toolchain` into `~/.lean_explore/cache/<version>`, recording it in
`~/.lean_explore/active_version`. Builds are dated snapshots (nightlies), not
Lean version tags, so **the LeanExplore index and your project's Mathlib pin are
independent** — semantic hits are candidates that must be confirmed against the
local environment with `lean-lsp-mcp`, exactly the flow KB.md specifies.

Pin a specific build with `lean-explore data fetch --version <YYYYMMDD_HHMMSS>`;
list what exists by fetching `manifest.json` from the R2 base URL in
`src/lean_explore/config.py`. `install.sh` reuses the version already recorded
in the manifest by default, so a reinstall reproduces the previous corpus
instead of silently jumping to the latest nightly.

**Recording is not pinning.** The manifest stores the embedding and reranker
commits read from HuggingFace's `refs/main`, but nothing forces `lean-explore`
to *load* those revisions on a later run — upstream resolves `main` itself. The
same holds for the data toolchain if you override the recorded version. This is
why the Scope table calls reproducibility *partial* rather than solved.

## The manifest: versions, and provenance

`.lean-kb-manifest.json` in the project root answers two different questions.

Most keys answer *what is installed*: resolved commits, tool versions, the
LeanExplore data toolchain, the effective `lake_jobs`.

The `provenance` map answers *what this skill did to get there*. Each component
carries two fields, and the distinction between them is the whole point:

```json
"lean_lsp_mcp": { "origin": "skill", "action": "preexisting" }
```

**`origin` answers the uninstall question.** `skill` means the component would
not exist but for this skill; `user` means it predated it; `shared` means it
lives outside the project in a machine-wide cache. Only `skill` is removable.

It is derived from the first action ever recorded and then sticky, because
otherwise one repair run destroys the answer: the run that installs `uv` records
`installed`, the next run sees `uv` already present and records `preexisting`,
and the fact that the skill created it is gone.

The one thing that *does* overwrite it is an `installing`/`installed` action.
Those are chosen only when the before-state check found the component missing,
so this run created what is there now — whatever an older, since-removed copy
used to belong to.

**`action` is what the latest run did**, and mutations are bracketed:

| Action | Meaning | `origin` it implies when first seen |
|---|---|---|
| `installing` | creating it; **may be half-created** if the run died here | `skill` |
| `installed` | created by this run | `skill` |
| `replacing` | overwriting it; **may be half-overwritten** | `user` |
| `replaced` | existed before and was overwritten | `user` |
| `reused` | existed before, deliberately used as-is | `user` |
| `preexisting` | existed before; the run only detected it | `user` |
| `absent` | the stage ran and the component is not installed | none — see below |

Only `origin: skill` is safe to remove on an uninstall. `replaced` is the worst
case: the component is the user's, and the version the skill overwrote is not
recoverable.

Three components are always `origin: shared` regardless of who triggered the
download, because they live in machine-wide caches other projects and tools
read: `lean_toolchain` (`~/.elan/toolchains`, ~2.8 GiB per Lean version) and
`hf_embedding_model` / `hf_reranker_model` (`~/.cache/huggingface`). Causing a
download does not make it ours to delete.

Five consequences worth knowing:

- **The in-flight verbs exist because failure is when this matters.** Recording
  only on success leaves a partial mutation invisible — a require appended and
  then unbuildable, an MCP registration removed and then not re-added. Those
  runs never reach the end of the script.
- **A caught failure writes no settled action at all**, leaving the in-flight
  one standing. A failed `lake build repl` must not record `absent`: `lake
  update` may have left a checkout, complete or not, so absence is not
  established — and `absent` resets the origin, which would erase the fact that
  the skill put it there.
- **A run that aborts still writes the manifest**, from an EXIT trap, for the
  same reason.
- **Entries are never cleared by stage.** A stage that starts and fails reports
  nothing; dropping its history on that basis would erase the record of what an
  earlier run created. (The *version* keys do use stage ownership — but keyed on
  stages that ran **to completion**, listed in `stages_completed`. A stage that
  died partway appears in `stages_incomplete` and clears nothing.)
- **`absent` resets `origin`.** If the component is gone, the next run's
  observation starts fresh, so a user who reinstalls it by hand is not recorded
  as `skill` on the strength of an install that no longer exists.

MCP entries are keyed **`mcp_<server>.<scope>`** — `mcp_lean_lsp.project`,
`mcp_lean_lsp.user` — and repeat the scope as a field. `project`, `local`, and
`user` are separate objects in separate files; sharing one key would let a
user-scoped registration inherit the skill-owned origin of an unrelated
project-scoped one, and an uninstall would then delete the user's.

For the same reason the before-state probe is `introspect.py mcp-registered
--scope`, which reads the file that scope actually writes, not `claude mcp get`,
which resolves across all three.

## Two traps that produce false confidence

**`lean-explore search` is the hosted API, not the local backend.** The CLI
`search` subcommand constructs an `ApiClient()`, which raises `ValueError`
without `LEANEXPLORE_API_KEY`; it has no `--backend` flag. Only
`lean-explore mcp serve --backend local` uses the local index. Testing a local
install with the CLI either fails spuriously (no key) or silently verifies the
wrong backend (with a key). `install.sh` and `verify.sh` therefore both drive the
local backend through `mcp_smoke.py`.

**A successful `lean_loogle` query does not prove local Loogle is active.** It
falls back to the remote API silently on any local failure, including an OOM
during indexing. The only evidence is this project's own index file, whose name
is `mathlib-<sha256(resolved project path)[:12]>.idx` — so a glob over the shared
cache can match a *different* project's index and report a false pass. Use
`introspect.py loogle-index <project>`, which reproduces upstream's key exactly.

## Extending toward KB.md

This skill installs the *stock* pipeline and nothing more; see the Scope table in
`SKILL.md` for what KB.md requires that is not delivered. The largest gap is that
project-local declarations are absent from the search corpus — the LeanExplore
index is a prebuilt Mathlib snapshot on a nightly cadence unrelated to your
Mathlib pin.

The extension point is LeanExplore's own extraction pipeline
(`src/lean_explore/extract/`, `pip install lean-explore[extract]`), which builds a
database plus FAISS index from a Lean project. That is a separate build step, and
the place where KB.md's unified corpus, source-reference metadata, and incremental
indexing would have to be implemented.

## Troubleshooting

| Symptom | Cause | Fix |
|---|---|---|
| `lean_local_search` errors | ripgrep missing | `install.sh --only ripgrep --allow-sudo` |
| Loogle answers but no `.idx` | indexing OOMed, silently using the remote API | raise RAM, or `--skip loogle` to accept remote on purpose |
| `lean-explore search` says no API key | that CLI is API-only by design | test the local backend via `mcp serve --backend local` |
| Loogle `.idx` exists but queries are rate-limited | the index belongs to another project path | check `introspect.py loogle-index <project>` |
| Mathlib require rejected as "moving branch" | pinned to `master`/`main` | set a release tag or commit; KB.md requires a fixed pin |
| MCP server "failed to connect" | Claude Code launched it without `~/.local/bin` on PATH | `install.sh --only register` — it registers absolute paths |
| `lake exe cache get` fails | network, or a Mathlib rev with no published cache | re-run; `lake build` will compile from source, slowly |
| No Mathlib tag for the toolchain | project on a nightly or rc | move to a released toolchain, or pin Mathlib by hand |
| `import Mathlib` times out in verify | Mathlib not fully built | `install.sh --only mathlib` |
| `lake build` killed with no error | OOM: too many workers for the RAM | lower `--lake-jobs`; check `lake_jobs` in the manifest |
| Preflight says a host is unreachable | genuinely offline, or a proxy blocking HEAD | `curl -I <url>` by hand to confirm |
