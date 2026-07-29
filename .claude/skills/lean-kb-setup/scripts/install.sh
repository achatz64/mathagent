#!/usr/bin/env bash
# Install the local Lean knowledge-base *prerequisites*. Every stage is
# idempotent, so re-running after a failure resumes rather than redoes.
#
# This installs tooling. It does not build the KB.md knowledge base — see the
# "Scope" section of SKILL.md.
#
# Usage:
#   install.sh [--project DIR] [--only STAGES] [--skip STAGES]
#              [--allow-sudo] [--mcp-scope project|local|user]
#              [--le-data-version YYYYMMDD_HHMMSS] [--lake-jobs N]
#
#   --lake-jobs  parallel Lake workers. Defaults to the smaller of the core
#                count and what RAM can feed (~2 GiB per worker when Mathlib
#                compiles from source). Also settable as LEAN_KB_LAKE_JOBS.
#
# Stages, in order:
#   uv           uv (userspace, no sudo)
#   elan         Lean toolchain manager (userspace, no sudo)
#   ripgrep      required by lean_local_search / lean_verify (needs sudo)
#   mathlib      pin + fetch + build Mathlib in the target project
#   repl         pin + build leanprover-community/repl for fast run_code
#   leanlsp      lean-lsp-mcp via uv
#   loogle       build the local Loogle binary and its Mathlib index
#   leanexplore  lean-explore[local] + prebuilt semantic index + models
#   register     register both MCP servers with Claude Code
#
# Anything needing root or a host restart is printed for approval, never run,
# unless --allow-sudo is passed.

set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/common.sh"

PROJECT="$PWD"
ONLY=""; SKIP=""; ALLOW_SUDO=0; MCP_SCOPE="project"; LE_DATA_PIN=""
LAKE_JOBS="${LEAN_KB_LAKE_JOBS:-}"

while [ $# -gt 0 ]; do
  case "$1" in
    --project)          PROJECT="$2"; shift 2 ;;
    --only)             ONLY="$2"; shift 2 ;;
    --skip)             SKIP="$2"; shift 2 ;;
    --allow-sudo)       ALLOW_SUDO=1; shift ;;
    --mcp-scope)        MCP_SCOPE="$2"; shift 2 ;;
    --le-data-version)  LE_DATA_PIN="$2"; shift 2 ;;
    --lake-jobs)        LAKE_JOBS="$2"; shift 2 ;;
    -h|--help)          sed -n '2,30p' "$0"; exit 0 ;;
    *) die "unknown argument: $1" ;;
  esac
done

ALL_STAGES="uv elan ripgrep mathlib repl leanlsp loogle leanexplore register"

# A typo in --only used to install nothing and still report success.
for s in $ONLY $SKIP; do
  case " $ALL_STAGES " in
    *" $s "*) ;;
    *) die "unknown stage '$s' — valid stages: $ALL_STAGES" ;;
  esac
done
case "$MCP_SCOPE" in
  project|local|user) ;;
  *) die "invalid --mcp-scope '$MCP_SCOPE' — use project, local, or user" ;;
esac

# An explicit job count is honoured as given — the operator may know something
# the RAM heuristic does not — but it still has to be a positive integer, or
# `lake build -j ""` fails deep inside the longest stage.
case "$LAKE_JOBS" in
  "")       ;;
  *[!0-9]*) die "invalid --lake-jobs '$LAKE_JOBS' — expected a positive integer" ;;
  *)        # 10# forces base 10, so "00" is rejected as zero rather than
            # accepted as a digit string, and "08" is 8 rather than an error.
            LAKE_JOBS=$((10#$LAKE_JOBS))
            [ "$LAKE_JOBS" -ge 1 ] || die "invalid --lake-jobs — expected a positive integer" ;;
esac

wanted() {
  case " $SKIP " in *" $1 "*) return 1 ;; esac
  [ -z "$ONLY" ] && return 0
  case " $ONLY " in *" $1 "*) return 0 ;; esac
  return 1
}

# `--skip loogle` is the one explicit way to ask for the remote Loogle API, so
# the register stage treats it as consent. Anything else with no local index is
# an accident and stops the install.
skipped_loogle() { case " $SKIP " in *" loogle "*) return 0 ;; esac; return 1; }

OS="$(os_kind)"
[ "$OS" = unsupported ] && die "unsupported platform $(uname -s) — use Linux, macOS, or WSL2"
have python3 || die "python3 is required by this skill's helper scripts"

PROJ="$(find_lean_project "$PROJECT")" || die "no Lean project (lean-toolchain) at or above $PROJECT"
REPO_ROOT="$(git -C "$PROJ" rev-parse --show-toplevel 2>/dev/null || echo "$PROJ")"

# uv and elan install into these; they are not on PATH until a new shell starts,
# so every later stage addresses them by absolute path.
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"

MANIFEST="$PROJ/.lean-kb-manifest.json"
STARTED_STAGES=""; DONE_STAGES=""

if [ -z "$LAKE_JOBS" ]; then
  LAKE_JOBS="$(lake_jobs_default)"
  JOBS_SOURCE="derived from $(ram_gib) GiB RAM and $(cpu_count) cores"
else
  JOBS_SOURCE="requested"
fi

# Installation provenance. The version manifest says what is installed; this
# says how it got there, so a later uninstall knows what it may remove and what
# predates the skill.
#
# Every mutation is bracketed: an in-flight action is recorded *before* it
# starts and the settled one after it succeeds. A stage killed halfway leaves
# the in-flight marker, which is the honest record — `installing` means "this
# may be half-created", `replacing` means "something of the user's may be half
# overwritten". Recording only on success would leave a partial mutation
# invisible, and that is the case an uninstall most needs to know about.
#
# Actions: installing/installed | replacing/replaced | reused | preexisting |
# absent. introspect.py derives the sticky `origin` from them; see reference.md.
PROVENANCE=""
prov() { # component, action, [detail]
  PROVENANCE="${PROVENANCE}$1 $2 ${3:-}
"
}

# A stage that catches its own error and carries on still did not finish. Its
# manifest keys must not be cleared as if it had, and it belongs in
# stages_incomplete — otherwise a swallowed failure reads as a clean run.
STAGE_FAILED=0
stage_failed() { STAGE_FAILED=1; }

# Resolved facts, filled in by whichever stages actually run.
MATHLIB_INPUTREV=""; MATHLIB_REV=""; MATHLIB_URL=""
REPL_INPUTREV=""; REPL_REV=""
LOOGLE_INDEX=""; LE_DATA_VERSION=""
EMBED_REV=""; RERANK_REV=""

introspect() { python3 "$HERE/introspect.py" "$@"; }

# The exact index file for this project, never a glob over the shared cache.
# `loogle-index` always succeeds, so computing the path cannot abort the script
# just because the index has not been built yet.
loogle_index_json() {
  if [ -n "${LEAN_LOOGLE_CACHE_DIR:-}" ]; then
    introspect loogle-index "$PROJ" --cache-dir "$LEAN_LOOGLE_CACHE_DIR"
  else
    introspect loogle-index "$PROJ"
  fi
}
loogle_index_path()   { loogle_index_json | jget path; }
loogle_index_exists() { [ "$(loogle_index_json | jget exists)" = "True" ]; }

# ------------------------------------------------------------------- uv ----

stage_uv() {
  step "uv"
  if have uv; then
    prov uv preexisting
    pass "already installed ($(uv --version | awk '{print $2}'))"
    return
  fi
  prov uv installing
  if [ "$(pkg_manager)" = brew ]; then
    brew install uv
  else
    curl -LsSf https://astral.sh/uv/install.sh | sh
  fi
  have uv || die "uv install did not put uv on PATH"
  prov uv installed
  pass "installed $(uv --version | awk '{print $2}')"
}

# ----------------------------------------------------------------- elan ----

stage_elan() {
  step "elan"
  if have elan; then
    prov elan preexisting
    pass "already installed ($(elan --version | awk '{print $2}'))"
    return
  fi
  prov elan installing
  curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
  have elan || die "elan install did not put elan on PATH"
  prov elan installed
  pass "installed $(elan --version | awk '{print $2}')"
}

# -------------------------------------------------------------- ripgrep ----

stage_ripgrep() {
  step "ripgrep"
  if have rg; then
    prov ripgrep preexisting
    pass "already installed ($(rg --version | head -1 | awk '{print $2}'))"
    return
  fi
  cmd="$(pkg_install_cmd ripgrep)"
  [ -z "$cmd" ] && { prov ripgrep absent; warn "no known package manager — install ripgrep manually"; return; }
  if [ "$ALLOW_SUDO" -eq 1 ] || [ "$(pkg_manager)" = brew ]; then
    prov ripgrep installing
    # Safe to hand to a shell: $cmd is one of pkg_install_cmd's fixed literals,
    # which need a shell for the `&&`. No path or file content reaches it.
    sh -c "$cmd"
    prov ripgrep installed
    pass "installed $(rg --version | head -1 | awk '{print $2}')"
  else
    prov ripgrep absent
    warn "needs root, skipped. Run this, then re-run with --only ripgrep:"
    note "$cmd"
  fi
}

# --------------------------------------------------------- Lean packages ----
#
# Pins come from the project's own lean-toolchain and are validated rather than
# assumed: an existing `mathlib` mention in a lakefile is not evidence of a
# reproducible pin, which is what KB.md actually requires.

append_require() { # name, git url, rev
  cat >>"$PROJ/lakefile.toml" <<EOF

[[require]]
name = "$1"
git = "$2"
rev = "$3"
EOF
  pass "added require $1 @ $3"
}

resolve_tag() { # repo url -> tag matching the project toolchain, or fail
  tag="$(toolchain_tag "$PROJ")"
  [ -z "$tag" ] && return 1
  git_tag_exists "$1" "$tag" || return 1
  echo "$tag"
}

# Validate an existing require block, or add one. Sets ENSURE_REV rather than
# echoing: a `die` inside a command substitution only kills the subshell, so
# the caller would sail past a fatal error.
#
# Returns 0 pinned (ENSURE_REV set), 1 no matching release tag, 2 fatal.
# ENSURE_ACTION records whether the require was already in the lakefile or
# written by this run — the lakefile is a user-owned file, so an uninstall must
# know which of the two it is looking at.
ENSURE_REV=""; ENSURE_ACTION=""
ensure_pinned() { # name, git url, human label
  name="$1"; url="$2"; label="$3"
  ENSURE_REV=""; ENSURE_ACTION=""

  # `if` suppresses errexit for the command it tests, so the status can be
  # captured without `set +e` — which, being global, would otherwise clobber
  # the caller's own errexit handling when this function re-enabled it.
  if req="$(introspect require "$PROJ" "$name" 2>/dev/null)"; then rc=0; else rc=$?; fi
  if [ "$rc" = 2 ]; then
    # A malformed lakefile must not read as "no such require" — that would
    # append a duplicate block on top of the damage.
    fail "cannot parse $PROJ/lakefile.toml: $(printf '%s' "$req" | jget error)"
    return 2
  fi

  if [ "$rc" = 0 ]; then
    rev="$(printf '%s' "$req" | jget rev)"
    url_declared="$(printf '%s' "$req" | jget git)"
    if [ -z "$url_declared" ]; then
      fail "$label require has no git URL — cannot verify what it points at"
      return 2
    fi

    case "$(classify_ref "$url_declared" "$rev")" in
      commit) pass "$label pinned at commit ${rev%"${rev#??????????}"}…" ;;
      tag)    pass "$label pinned at tag $rev" ;;
      head)
        fail "$label is required at '$rev', which is a branch on $url_declared"
        note "KB.md requires a reproducible pin — set a tag or commit in"
        note "$PROJ/lakefile.toml, then re-run"
        return 2 ;;
      unknown)
        fail "$label is required at '$rev', which is neither a tag nor a branch on $url_declared"
        note "check the revision, or pin a full 40-character commit"
        return 2 ;;
      offline)
        warn "$label pinned at '$rev' but $url_declared is unreachable — cannot verify"
        note "proceeding; re-run with network access to confirm the pin" ;;
    esac

    tag="$(toolchain_tag "$PROJ")"
    if [ -n "$tag" ] && [ "$rev" != "$tag" ]; then
      warn "$label is at $rev but the toolchain wants $tag — verify they are compatible"
    fi
    ENSURE_REV="$rev"; ENSURE_ACTION=preexisting
    prov "${name}_require" preexisting
    return 0
  fi

  rev="$(resolve_tag "$url")" || return 1
  # Bracketed here rather than in the caller: append_require edits a file the
  # user owns, and the record has to exist before the edit does.
  prov "${name}_require" installing
  append_require "$name" "$url" "$rev"
  ENSURE_REV="$rev"; ENSURE_ACTION=installed
  prov "${name}_require" installed
  return 0
}

# set -e would abort on the non-zero returns above, and a command substitution
# would strand ENSURE_REV in a subshell, so callers run it in the current shell
# with errexit briefly disabled.
PIN_RC=0
try_pin() { # name, git url, label
  set +e
  ensure_pinned "$1" "$2" "$3"
  PIN_RC=$?
  set -e
}

stage_mathlib() {
  step "Mathlib"

  # Previously this warned and then carried on to build and report success.
  if [ ! -f "$PROJ/lakefile.toml" ]; then
    die "this stage only edits lakefile.toml, but $PROJ uses lakefile.lean.
      Add the Mathlib require by hand, then re-run with --skip mathlib."
  fi

  # Recorded before anything is written, so the manifest reflects the state
  # this run found rather than the state it produced.
  if [ -d "$PROJ/.lake/packages/mathlib" ]; then had_pkg=1; else had_pkg=0; fi

  try_pin mathlib https://github.com/leanprover-community/mathlib4 Mathlib
  case "$PIN_RC" in
    0) MATHLIB_INPUTREV="$ENSURE_REV" ;;
    2) exit 1 ;;  # already reported; a moving pin is not something to work around
    *) die "no Mathlib release tag matches toolchain '$(tr -d '\r' <"$PROJ/lean-toolchain")' — pin it manually" ;;
  esac

  if [ "$had_pkg" -eq 1 ]; then prov mathlib_packages replacing; else prov mathlib_packages installing; fi

  # The first lake invocation makes elan download the pinned toolchain (~2.8
  # GiB) if it is not already there. It lands in ~/.elan/toolchains, shared with
  # every other project on this machine, so it is recorded as `shared`.
  tc="$(tr -d '\r' <"$PROJ/lean-toolchain")"
  if elan toolchain list 2>/dev/null | grep -qF "$tc"; then had_tc=1; else had_tc=0; fi
  if [ "$had_tc" -eq 0 ]; then prov lean_toolchain installing; fi

  step "Mathlib: resolving dependencies (lake update)"
  (cd "$PROJ" && lake update)

  # Mathlib's own binary cache. Without it this stage compiles Mathlib from
  # source, which is hours rather than minutes.
  step "Mathlib: fetching the build cache (multi-GB, slow)"
  if ! (cd "$PROJ" && lake exe cache get); then
    warn "'lake exe cache get' failed — 'lake build' will compile Mathlib from source"
    note "that is when -j matters: $LAKE_JOBS workers x ~${RAM_PER_LAKE_JOB} GiB against $(ram_gib) GiB"
  fi

  step "Mathlib: lake build (-j $LAKE_JOBS)"
  (cd "$PROJ" && lake build -j "$LAKE_JOBS")

  # `replaced`, not `preexisting`: lake update + build ran over what was there.
  # `preexisting` means "detected, untouched", which is not what happened.
  if [ "$had_pkg" -eq 1 ]; then prov mathlib_packages replaced; else prov mathlib_packages installed; fi
  if [ "$had_tc"  -eq 1 ]; then prov lean_toolchain   preexisting; else prov lean_toolchain   installed; fi


  # The commit Lake actually resolved is the reproducibility lock; the tag is
  # only what we asked for.
  if res="$(introspect resolved "$PROJ" mathlib 2>/dev/null)"; then
    MATHLIB_REV="$(printf '%s' "$res" | jget rev)"
    MATHLIB_URL="$(printf '%s' "$res" | jget url)"
    pass "Mathlib built, resolved to ${MATHLIB_REV:-unknown}"
  else
    warn "Mathlib built but not found in lake-manifest.json"
  fi
}

# What repl provenance should say when this stage did not build anything: look,
# do not assert. `absent` resets the origin, so claiming it over a checkout that
# is actually present would erase who put it there.
prov_repl_observed() {
  if [ -d "$PROJ/.lake/packages/repl" ] || [ -d "$PROJ/.lake/packages/REPL" ]; then
    prov repl_packages preexisting
  else
    prov repl_packages absent
  fi
}

stage_repl() {
  step "Lean REPL"
  if [ ! -f "$PROJ/lakefile.toml" ]; then
    # Observed, not assumed: a lakefile.lean project may already have repl
    # fetched, and `absent` would reset the origin of something that is there.
    prov_repl_observed
    warn "project uses lakefile.lean — add the repl require yourself; skipping"
    stage_failed
    return
  fi
  if [ -d "$PROJ/.lake/packages/repl" ] || [ -d "$PROJ/.lake/packages/REPL" ]; then
    had_repl=1
  else
    had_repl=0
  fi

  try_pin repl https://github.com/leanprover-community/repl "Lean REPL"
  case "$PIN_RC" in
    0) REPL_INPUTREV="$ENSURE_REV" ;;
    2) exit 1 ;;
    *) warn "no repl tag matches this toolchain — skipping (lean-lsp-mcp falls back to the LSP)"
       prov_repl_observed
       stage_failed
       return ;;
  esac

  if [ "$had_repl" -eq 1 ]; then prov repl_packages replacing; else prov repl_packages installing; fi
  (cd "$PROJ" && lake update repl) || true
  if ! (cd "$PROJ" && lake build -j "$LAKE_JOBS" repl); then
    # Deliberately no settled action: `lake update` may have left a checkout,
    # complete or not, so "absent" is not established. The in-flight marker
    # stands, which is the truthful record of a mutation that never finished.
    stage_failed
    warn "repl build failed — LSP fallback still works"
    return
  fi
  if [ "$had_repl" -eq 1 ]; then prov repl_packages replaced; else prov repl_packages installed; fi
  if res="$(introspect resolved "$PROJ" repl 2>/dev/null)"; then
    REPL_REV="$(printf '%s' "$res" | jget rev)"
  fi
  pass "repl built, resolved to ${REPL_REV:-unknown}"
}

# -------------------------------------------------------------- leanlsp ----

stage_leanlsp() {
  step "lean-lsp-mcp $LEAN_LSP_MCP_VERSION"
  # --force overwrites whatever version was there, so note first whether there
  # was one: `replaced` and `installed` mean different things to an uninstall.
  if have lean-lsp-mcp; then had_lsp=1; else had_lsp=0; fi
  if [ "$had_lsp" -eq 1 ]; then prov lean_lsp_mcp replacing; else prov lean_lsp_mcp installing; fi

  # Installed as a tool rather than run through bare uvx so the version is
  # materialised on disk and the server keeps starting with no network.
  uv tool install --force "lean-lsp-mcp==$LEAN_LSP_MCP_VERSION"
  bin="$(command -v lean-lsp-mcp || echo "$HOME/.local/bin/lean-lsp-mcp")"
  [ -x "$bin" ] || die "lean-lsp-mcp not found after install"
  if [ "$had_lsp" -eq 1 ]; then prov lean_lsp_mcp replaced; else prov lean_lsp_mcp installed; fi
  pass "installed at $bin"
}

# --------------------------------------------------------------- loogle ----
#
# The server builds and indexes lazily on first query, behind fixed internal
# timeouts (900s build, 300s index). Doing it here, in the foreground and
# without those timeouts, turns a silent remote-fallback into a visible error.
#
# No fallback: this stage either produces a local index or stops the install.
# The failure it exists to catch is an OOM during indexing, after which
# `lean_loogle` answers from the remote API and looks like it worked. Degrading
# to that silently is the outcome the whole stage is here to prevent, so it is
# a hard error. `--skip loogle` is the way to ask for the remote API on purpose.

stage_loogle() {
  step "local Loogle index"

  ram="$(ram_gib)"
  if lt "$ram" "$NEED_RAM_LOOGLE_INDEX"; then
    warn "${ram} GiB RAM; the initial index needs ~13 GiB peak RSS"
    note "attempting anyway — if it OOMs this stage stops the install"
  fi

  [ -d "$PROJ/.lake/packages/mathlib" ] || die "no Mathlib in $PROJ, so local Loogle has nothing to index.
      Run the mathlib stage first, or --skip loogle to use the remote API."
  have lean-lsp-mcp || die "lean-lsp-mcp is not installed, so the Loogle index cannot be built.
      Run the leanlsp stage first, or --skip loogle to use the remote API."

  # Before-state for provenance: the server builds and indexes lazily, so both
  # artefacts may already exist from an earlier run or another tool.
  cache="${LEAN_LOOGLE_CACHE_DIR:-$HOME/.cache/lean-lsp-mcp/loogle}"
  if ls -1 "$cache"/repo-*/.lake/build/bin/loogle >/dev/null 2>&1; then had_bin=1; else had_bin=0; fi
  if loogle_index_exists; then had_idx=1; else had_idx=0; fi
  if [ "$had_bin" -eq 1 ]; then prov loogle_binary replacing; else prov loogle_binary installing; fi
  if [ "$had_idx" -eq 1 ]; then prov loogle_index replacing; else prov loogle_index installing; fi

  expected="$(loogle_index_path)"
  export LEAN_LOOGLE_LOCAL=true
  # So a remote answer cannot stand in for a local one during this probe.
  export LOOGLE_URL="$LOOGLE_NULL_BACKEND"

  # A tools/call to lean_loogle drives the whole lazy path: clone, build under
  # the project's toolchain, then index the project's Mathlib.
  # Not fatal on its own: the call itself can fail while the index still lands,
  # and the index file is the only thing that actually settles the question.
  if ! python3 "$HERE/mcp_smoke.py" --timeout 3600 --quiet \
        --call lean_loogle --args '{"query": "Nat.add_comm", "num_results": 1}' \
        -- "$(command -v lean-lsp-mcp)" --lean-project-path "$PROJ" --loogle-local >/dev/null; then
    warn "the lean_loogle call failed — checking for the index anyway"
  fi

  # A successful query proves nothing: lean_loogle falls back to the remote API
  # silently. Only this project's own index file is evidence.
  # `absent` is only truthful when nothing was there before either — it resets
  # the origin, so claiming it after destroying something of the user's would
  # erase that fact. When the before-state was present and the artefact is now
  # gone, leave the in-flight marker standing.
  if ls -1 "$cache"/repo-*/.lake/build/bin/loogle >/dev/null 2>&1; then
    if [ "$had_bin" -eq 1 ]; then prov loogle_binary preexisting; else prov loogle_binary installed; fi
  elif [ "$had_bin" -eq 0 ]; then
    prov loogle_binary absent
  fi

  if ! loogle_index_exists; then
    if [ "$had_idx" -eq 0 ]; then prov loogle_index absent; fi
    fail "no index at $expected — local Loogle is NOT active"
    note "almost always an OOM during indexing: the peak is ~13 GiB and this host has ${ram} GiB"
    note "lean_loogle would answer from the remote API (3 req/30s) and look like it worked,"
    note "so this is a hard stop. Raise available RAM, or --skip loogle to accept the remote API."
    die "local Loogle index was not built"
  fi

  LOOGLE_INDEX="$expected"
  if [ "$had_idx" -eq 1 ]; then prov loogle_index preexisting; else prov loogle_index installed; fi
  pass "index built: $LOOGLE_INDEX ($(du -h "$LOOGLE_INDEX" | awk '{print $1}'))"
}

# ---------------------------------------------------------- lean-explore ----

stage_leanexplore() {
  step "lean-explore $LEAN_EXPLORE_VERSION (local backend)"

  if have lean-explore; then had_le=1; else had_le=0; fi
  if [ "$had_le" -eq 1 ]; then prov lean_explore replacing; else prov lean_explore installing; fi

  # On Linux the default torch wheel drags in ~2 GiB of CUDA runtime. Ask uv
  # for CPU wheels when there is no NVIDIA GPU; fall back if uv is too old to
  # understand the flag. This is a disk optimisation — nothing here needs a GPU.
  if [ "$OS" != macos ] && ! have nvidia-smi; then
    UV_TORCH_BACKEND=cpu uv tool install --force "lean-explore[local]==$LEAN_EXPLORE_VERSION" \
      || uv tool install --force "lean-explore[local]==$LEAN_EXPLORE_VERSION"
  else
    uv tool install --force "lean-explore[local]==$LEAN_EXPLORE_VERSION"
  fi

  le="$(command -v lean-explore || echo "$HOME/.local/bin/lean-explore")"
  [ -x "$le" ] || die "lean-explore not found after install"
  if [ "$had_le" -eq 1 ]; then prov lean_explore replaced; else prov lean_explore installed; fi

  # Reuse the recorded data version by default so a reinstall reproduces the
  # previous corpus instead of silently jumping to the latest nightly.
  pin="$LE_DATA_PIN"
  if [ -z "$pin" ] && [ -f "$MANIFEST" ]; then
    pin="$(jget lean_explore_data <"$MANIFEST" 2>/dev/null || true)"
  fi

  active="$HOME/.lean_explore/active_version"
  # Whether *any* data toolchain is already installed, which is a different
  # question from whether the wanted one is: fetching over a different version
  # is a replacement, not a fresh install, and only the latter may claim
  # `installing` — that action asserts the before-state was empty.
  if [ -f "$active" ] && [ -f "$HOME/.lean_explore/cache/$(cat "$active")/lean_explore.db" ]; then
    had_data=1
  else
    had_data=0
  fi

  step "lean-explore: fetching the prebuilt index (~3.9 GiB)"
  if [ "$had_data" -eq 1 ] && { [ -z "$pin" ] || [ "$(cat "$active")" = "$pin" ]; }; then
    LE_DATA_VERSION="$(cat "$active")"
    prov lean_explore_data reused
    pass "data toolchain $LE_DATA_VERSION already present"
  else
    if [ "$had_data" -eq 1 ]; then prov lean_explore_data replacing; else prov lean_explore_data installing; fi
    if [ -n "$pin" ]; then
      "$le" data fetch --version "$pin"
    else
      "$le" data fetch
    fi
    LE_DATA_VERSION="$(cat "$active" 2>/dev/null || echo '')"
    if [ "$had_data" -eq 1 ]; then prov lean_explore_data replaced; else prov lean_explore_data installed; fi
    pass "data toolchain ${LE_DATA_VERSION:-unknown}"
  fi

  # The warm-up downloads the two Qwen3 models into the shared HuggingFace
  # cache, which other tools on this machine use too. Recorded, but as `shared`
  # — see reference.md — so no uninstall ever treats them as ours to delete.
  if introspect hf-revision Qwen/Qwen3-Embedding-0.6B >/dev/null 2>&1; then had_embed=1; else had_embed=0; fi
  if introspect hf-revision Qwen/Qwen3-Reranker-0.6B >/dev/null 2>&1; then had_rerank=1; else had_rerank=0; fi
  if [ "$had_embed"  -eq 0 ]; then prov hf_embedding_model installing; fi
  if [ "$had_rerank" -eq 0 ]; then prov hf_reranker_model  installing; fi

  # `lean-explore search` is the *hosted API* and needs LEANEXPLORE_API_KEY.
  # The local backend is only reachable through the MCP server, so warm and
  # prove it there. First call pulls the two Qwen3 models (~2.4 GiB).
  step "lean-explore: warming the local backend and its models"
  if python3 "$HERE/mcp_smoke.py" --timeout 1800 --quiet \
        --call search_summary --args '{"query": "commutativity of addition", "limit": 3}' \
        -- "$le" mcp serve --backend local >/dev/null; then
    warm_ok=1
    pass "local semantic search answering"
  else
    warm_ok=0
    warn "local backend did not answer — check: $le mcp serve --backend local"
    stage_failed
  fi

  EMBED_REV="$(introspect hf-revision Qwen/Qwen3-Embedding-0.6B 2>/dev/null | jget revision || true)"
  RERANK_REV="$(introspect hf-revision Qwen/Qwen3-Reranker-0.6B 2>/dev/null | jget revision || true)"

  # Only settle the models when the warm-up actually answered. `refs/main` can
  # exist after a partial download, so its presence is not proof the snapshot is
  # complete — and the caught-failure rule says the in-flight action stands.
  if [ "$warm_ok" -eq 1 ]; then
    if [ -n "$EMBED_REV" ]; then
      if [ "$had_embed" -eq 1 ]; then prov hf_embedding_model preexisting; else prov hf_embedding_model installed; fi
    elif [ "$had_embed" -eq 0 ]; then
      prov hf_embedding_model absent
    fi
    if [ -n "$RERANK_REV" ]; then
      if [ "$had_rerank" -eq 1 ]; then prov hf_reranker_model preexisting; else prov hf_reranker_model installed; fi
    elif [ "$had_rerank" -eq 0 ]; then
      prov hf_reranker_model absent
    fi
  fi
}

# ------------------------------------------------------------- register ----

# What a stage should record when it did not touch a registration: observe the
# actual state rather than asserting. "The binary is missing" is not evidence
# that nothing is registered — a stale entry from an earlier install may well
# be, and `absent` would reset its origin.
prov_mcp_observed() { # server name
  _k="mcp_$(printf '%s' "$1" | tr '-' '_').$MCP_SCOPE"
  case "$(introspect mcp-registered "$1" --scope "$MCP_SCOPE" --repo-root "$REPO_ROOT" | jget registered)" in
    True)  prov "$_k" preexisting "$MCP_SCOPE" ;;
    False) prov "$_k" absent      "$MCP_SCOPE" ;;
    *)     ;;  # unknown: record nothing rather than assert either way
  esac
}

stage_register() {
  step "registering MCP servers (scope: $MCP_SCOPE)"
  if ! have claude; then
    warn "claude CLI missing — registration not performed"
    prov_mcp_observed lean-lsp
    prov_mcp_observed lean-explore
    stage_failed
    return
  fi

  # Rollback operates on one registration at a whole-file level no longer:
  # `mcpServers.<name>` at the target scope is exactly what this skill writes,
  # and it is all it may undo. Restoring whole files could not touch
  # ~/.claude.json without reverting unrelated Claude Code state, so a failed
  # add there used to stay live — and prov_mcp_observed would then read that
  # skill-created entry back as someone else's `preexisting`.
  #
  # Non-zero when there is no usable before-state. `mcp-entry get` always exits
  # 0 — "I could not read it" is an answer, not a crash — so the caller has to
  # read `readable`. Taking an unreadable snapshot and registering anyway means
  # the undo is already impossible before the first write.
  mcp_snapshot() { # dir, name
    introspect mcp-entry get "$2" --scope "$MCP_SCOPE" --repo-root "$REPO_ROOT" >"$1/entry.json" || return 1
    [ "$(jget readable <"$1/entry.json")" = True ]
  }
  mcp_restore() { # dir, name
    if ! introspect mcp-entry restore "$2" --scope "$MCP_SCOPE" --repo-root "$REPO_ROOT" \
           --state-file "$1/entry.json" >/dev/null 2>&1; then
      warn "could not roll back the $2 registration — inspect $MCP_SCOPE scope by hand"
      return 1
    fi
    return 0
  }

  # Optional `-e KEY=VALUE` for the registered server, set by the caller.
  MCP_ENV=""
  mcp_add() { # name, command...
    _n="$1"; shift
    if [ -n "$MCP_ENV" ]; then
      (cd "$REPO_ROOT" && claude mcp add "$_n" -s "$MCP_SCOPE" -e "$MCP_ENV" -- "$@")
    else
      (cd "$REPO_ROOT" && claude mcp add "$_n" -s "$MCP_SCOPE" -- "$@")
    fi
  }

  # Replacing a registration means remove-then-add, and the add can still fail
  # (bad path, unwritable config). Snapshot the config first and roll back on
  # failure so a failed repair never leaves the user with no server at all.
  mcp_register() { # name, command...
    name="$1"; shift
    # Scope belongs in the *identity*, not just in a field: project, local, and
    # user registrations are separate objects in separate files. Sharing one key
    # would let a user-scoped registration inherit the skill-owned origin of an
    # unrelated project-scoped one, and an uninstall would then delete it.
    key="mcp_$(printf '%s' "$name" | tr '-' '_').$MCP_SCOPE"

    # Snapshot BEFORE anything is written — before the first add, not between
    # the two attempts. `claude mcp add` can modify the config and then fail, so
    # an add that runs outside the transaction has already put the rollback out
    # of reach. And if the snapshot cannot be taken, nothing may be written at
    # all: an unreadable config is the one case where a failed add cannot be
    # undone, which makes registering into it a one-way door.
    #
    # It is scope-exact, unlike `claude mcp get`, which resolves across all
    # three scopes and would make a fresh project-scoped registration look like
    # a replacement of an unrelated user-scoped one.
    backup="$(mktemp -d)"
    if ! mcp_snapshot "$backup" "$name"; then
      warn "cannot read the $MCP_SCOPE MCP config — refusing to register $name"
      note "$(jget error <"$backup/entry.json" 2>/dev/null)"
      note "a failed add could not be undone; fix $(jget source <"$backup/entry.json" 2>/dev/null) by hand"
      rm -rf "$backup"
      prov_mcp_observed "$name"
      return 1
    fi

    # The same read answers "was it already there?", so the before-state and the
    # rollback state can never disagree. The scope goes into the record too:
    # "lean-lsp is registered" is not actionable for an uninstall without it.
    if [ "$(jget present <"$backup/entry.json")" = True ]; then had=1; else had=0; fi
    if [ "$had" -eq 1 ]; then prov "$key" replacing "$MCP_SCOPE"; else prov "$key" installing "$MCP_SCOPE"; fi

    if mcp_add "$name" "$@" >/dev/null 2>&1; then
      rm -rf "$backup"
      if [ "$had" -eq 1 ]; then prov "$key" replaced "$MCP_SCOPE"; else prov "$key" installed "$MCP_SCOPE"; fi
      pass "$name registered"; return 0
    fi

    (cd "$REPO_ROOT" && claude mcp remove "$name" -s "$MCP_SCOPE" >/dev/null 2>&1) || true
    if mcp_add "$name" "$@"; then
      rm -rf "$backup"
      if [ "$had" -eq 1 ]; then prov "$key" replaced "$MCP_SCOPE"; else prov "$key" installed "$MCP_SCOPE"; fi
      pass "$name re-registered"; return 0
    fi

    # Re-probing is only legitimate once the config is back to what we
    # snapshotted. If the rollback failed — the file is still readable but no
    # longer writable, say — the entry sitting there may be the half-written one
    # this run produced, and prov_mcp_observed would read it back as
    # `preexisting`: a settled action that outranks the in-flight marker when
    # the manifest is merged, reclassifying our own mutation as something that
    # predated the skill. That is the precise evidence loss the bracketing
    # exists to prevent, so leave `installing`/`replacing` standing instead.
    if mcp_restore "$backup" "$name"; then
      rm -rf "$backup"
      prov_mcp_observed "$name"
      warn "$name registration failed; previous configuration restored"
    else
      rm -rf "$backup"
      fail "$name registration failed AND could not be rolled back"
      note "the $MCP_SCOPE config may still hold a partial registration from this run"
      note "provenance keeps its in-flight marker for $key; check it before removing anything"
    fi
    return 1
  }

  lsp_bin="$(command -v lean-lsp-mcp || true)"
  le_bin="$(command -v lean-explore || true)"

  # Absolute paths: Claude Code launches these without the login shell's PATH,
  # so ~/.local/bin is frequently not visible to it.
  if [ -n "$lsp_bin" ]; then
    # An array, so a project path containing spaces survives. And the loogle
    # flag is decided by looking at the index, not by whether this run happened
    # to include the loogle stage — `--only register` must not silently drop it.
    set -- --lean-project-path "$PROJ" --repl
    if loogle_index_exists; then
      set -- "$@" --loogle-local
      # Upstream falls back to the public Loogle API on any *runtime* local
      # failure, silently. Pointing LOOGLE_URL at a dead endpoint makes that
      # fall-through raise instead of quietly answering from the network.
      MCP_ENV="LOOGLE_URL=$LOOGLE_NULL_BACKEND"
      note "local Loogle index found; registering with --loogle-local"
      note "LOOGLE_URL pinned to a dead endpoint so a runtime fallback cannot go unnoticed"
    elif skipped_loogle; then
      # The user asked for the remote API by name. Leave LOOGLE_URL alone.
      MCP_ENV=""
      warn "no local Loogle index; registering WITHOUT --loogle-local (you passed --skip loogle)"
      note "lean_loogle will use the remote API, rate limited to 3 req/30s"
    else
      die "no local Loogle index, so registering lean-lsp would silently enable the
      remote API. Run the loogle stage, or pass --skip loogle to choose the
      remote API deliberately."
    fi
    mcp_register lean-lsp "$lsp_bin" "$@" || stage_failed
    MCP_ENV=""
  else
    prov_mcp_observed lean-lsp
    warn "lean-lsp-mcp not installed — not registered"
    stage_failed
  fi

  if [ -n "$le_bin" ]; then
    mcp_register lean-explore "$le_bin" mcp serve --backend local || stage_failed
  else
    prov_mcp_observed lean-explore
    warn "lean-explore not installed — not registered"
    stage_failed
  fi
}

# ------------------------------------------------------------- manifest ----
#
# KB.md requires reproducibility from pinned versions. This records the
# *resolved* commits, not just the tags asked for.

write_manifest() {
  values="$(
    MF_PROJECT="$PROJ" \
    MF_MATHLIB_INPUTREV="$MATHLIB_INPUTREV" MF_MATHLIB_REV="$MATHLIB_REV" MF_MATHLIB_URL="$MATHLIB_URL" \
    MF_REPL_INPUTREV="$REPL_INPUTREV" MF_REPL_REV="$REPL_REV" \
    MF_LEAN_LSP="$LEAN_LSP_MCP_VERSION" MF_LOOGLE_INDEX="$LOOGLE_INDEX" \
    MF_LE="$LEAN_EXPLORE_VERSION" MF_LE_DATA="$LE_DATA_VERSION" \
    MF_EMBED_REV="$EMBED_REV" MF_RERANK_REV="$RERANK_REV" \
    MF_SKILL="$SKILL_VERSION" MF_LAKE_JOBS="$LAKE_JOBS" MF_PROVENANCE="$PROVENANCE" \
    MF_STARTED="$STARTED_STAGES" MF_DONE="$DONE_STAGES" \
    python3 - <<'PY'
import datetime, json, os, pathlib, subprocess

def env(k):
    return os.environ.get(k) or None

def sh(*c):
    try:
        return subprocess.run(c, capture_output=True, text=True, timeout=30).stdout.strip() or None
    except Exception:
        return None

proj = pathlib.Path(os.environ["MF_PROJECT"])

# "component action [detail]" lines, every field emitted by install.sh itself.
# Passed through the environment rather than interpolated into this source.
# Later lines win, so the settled action supersedes the in-flight marker that
# preceded it — and survives alone if the mutation never finished.
prov = {}
for line in (os.environ.get("MF_PROVENANCE") or "").splitlines():
    parts = line.split()
    if len(parts) >= 2:
        entry = {"action": parts[1]}
        if len(parts) >= 3:
            entry["scope"] = parts[2]
        prov[parts[0]] = entry

done = (os.environ.get("MF_DONE") or "").split()
incomplete = [s for s in (os.environ.get("MF_STARTED") or "").split() if s not in done]

print(json.dumps({
    "generated":          datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "skill_version":      env("MF_SKILL"),
    "project":            str(proj),
    "lean_toolchain":     (proj / "lean-toolchain").read_text(encoding="utf-8").strip(),
    "lake_jobs":          int(os.environ["MF_LAKE_JOBS"]),
    "provenance":         prov,
    "stages_completed":   done,
    "stages_incomplete":  incomplete,
    "mathlib_inputrev":   env("MF_MATHLIB_INPUTREV"),
    "mathlib_rev":        env("MF_MATHLIB_REV"),
    "mathlib_url":        env("MF_MATHLIB_URL"),
    "repl_inputrev":      env("MF_REPL_INPUTREV"),
    "repl_rev":           env("MF_REPL_REV"),
    "lean_lsp_mcp":       env("MF_LEAN_LSP"),
    "loogle_index":       env("MF_LOOGLE_INDEX"),
    "lean_explore":       env("MF_LE"),
    "lean_explore_data":  env("MF_LE_DATA"),
    "embedding_model":    "Qwen/Qwen3-Embedding-0.6B",
    "embedding_revision": env("MF_EMBED_REV"),
    "reranker_model":     "Qwen/Qwen3-Reranker-0.6B",
    "reranker_revision":  env("MF_RERANK_REV"),
    "uv":                 (sh("uv", "--version") or "").strip() or None,
    "elan":               sh("elan", "--version"),
    "ripgrep":            (sh("rg", "--version") or "").split("\n")[0] or None,
}))
PY
  )"
  introspect write-manifest --out "$MANIFEST" --values "$values" --stages "$DONE_STAGES" >/dev/null
  pass "wrote $MANIFEST"
}

# ----------------------------------------------------------------- drive ----

# A run that aborts has usually already changed something — an appended
# require, an installed tool, a replaced MCP registration. Writing provenance
# only on success would lose it in exactly the cases where knowing what changed
# matters most, so record it from an EXIT trap too. Guarded on PROVENANCE being
# non-empty, so a run that died during validation leaves no manifest behind.
MANIFEST_WRITTEN=0
on_exit() {
  rc=$?
  if [ "$MANIFEST_WRITTEN" -eq 0 ] && [ -n "$PROVENANCE" ]; then
    MANIFEST_WRITTEN=1
    step "manifest (run did not finish — recording what it changed)"
    write_manifest || warn "could not write $MANIFEST"
  fi
  exit "$rc"
}
trap on_exit EXIT

# Started and completed are tracked separately. Only a stage that finished
# knows anything reliable about its manifest keys; clearing them on behalf of
# one that died partway would overwrite good recorded pins with nulls.
for s in $ALL_STAGES; do
  if wanted "$s"; then
    STARTED_STAGES="$STARTED_STAGES $s"
    STAGE_FAILED=0
    "stage_$s"
    if [ "$STAGE_FAILED" -eq 0 ]; then DONE_STAGES="$DONE_STAGES $s"; fi
  fi
done

step "manifest"
MANIFEST_WRITTEN=1
write_manifest

# A stage that swallowed its error must not let the run report success. The
# manifest already says which ones, and the exit status has to agree with it —
# otherwise a caller that checks `$?` is told everything worked.
INCOMPLETE=""
for s in $STARTED_STAGES; do
  case " $DONE_STAGES " in *" $s "*) ;; *) INCOMPLETE="$INCOMPLETE $s" ;; esac
done
if [ -n "$INCOMPLETE" ]; then
  printf '\n%sIncomplete stages:%s%s\n' "$C_R" "$C_N" "$INCOMPLETE" >&2
  note "see 'provenance' in $MANIFEST for what each one changed before stopping"
  exit 1
fi

printf '\n%sInstall finished.%s Run scripts/verify.sh to test it.\n' "$C_B" "$C_N"
