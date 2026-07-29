#!/usr/bin/env bash
# Probe the host and the target Lean project. Installs nothing, changes nothing.
#
# Exit 0  everything needed is present or installable by install.sh
# Exit 1  a hard blocker that install.sh cannot fix on its own
#
# Usage: preflight.sh [--project DIR]

set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/common.sh"

PROJECT="${PWD}"
while [ $# -gt 0 ]; do
  case "$1" in
    --project) PROJECT="$2"; shift 2 ;;
    -h|--help) sed -n '2,9p' "$0"; exit 0 ;;
    *) die "unknown argument: $1" ;;
  esac
done

# The same PATH install.sh and verify.sh use. uv and elan install into these
# directories and are not on PATH until a new login shell starts, so without
# this preflight reports tools as missing that install.sh can already see —
# and then proposes installing them again.
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"

OS="$(os_kind)"
RAM="$(ram_gib)"
RAM_AVAIL="$(ram_available_gib 2>/dev/null || true)"
SWAP="$(swap_gib 2>/dev/null || true)"
CPUS="$(cpu_count)"

# Resolved here rather than in the "Lean project" section further down, because
# the memory section reports on it: whether this project's index already exists
# decides whether a resource-intensive first build is still ahead. That is a
# statement about *state*, which is knowable — unlike a statement about whether
# the host can afford it, which is not.
#
# Both are "no" answers, not errors: a run with no project yet, or with no index
# yet, is simply one where the first build has not happened.
LOOGLE_INDEXED=0
if PRE_PROJ="$(find_lean_project "$PROJECT" 2>/dev/null)"; then
  if [ "$(python3 "$HERE/introspect.py" loogle-index "$PRE_PROJ" 2>/dev/null | jget exists)" = True ]; then
    LOOGLE_INDEXED=1
  fi
else
  PRE_PROJ=""
fi

# --------------------------------------------------------------- platform ---

section "Platform"

case "$OS" in
  linux) pass "Linux, $CPUS cores" ;;
  macos) pass "macOS, $CPUS cores" ;;
  wsl)   pass "WSL2, $CPUS cores"
         note "local Loogle is Unix-only; WSL2 satisfies that, native Windows does not" ;;
  *)     fail "unsupported platform: $(uname -s)"
         note "this stack needs Linux, macOS, or WSL2 — on Windows, run inside WSL2"
         summary "Preflight" || exit 1 ;;
esac

for t in git curl; do
  if have "$t"; then pass "$t present"; else fail "$t missing — install it first"; fi
done

# install.sh and verify.sh both drive MCP servers through Python helpers.
if have python3; then
  pyver="$(python3 -c 'import sys; print("%d.%d" % sys.version_info[:2])' 2>/dev/null || echo 0.0)"
  if lt "$pyver" 3.10; then
    fail "python3 is $pyver — this skill's helpers need 3.10+"
  else
    pass "python3 $pyver"
  fi
else
  fail "python3 missing — required by introspect.py and mcp_smoke.py"
fi

# ---------------------------------------------------------------- memory ----

section "Memory"

# Observations only. This skill holds no memory thresholds, so nothing below is
# a PASS or a FAIL: what the stack costs depends on the pinned Mathlib and
# LeanExplore versions, the model implementation, the query, the OS and whatever
# else is resident, none of which a constant in this repo can track. A verdict
# from a stale number is worse than no verdict — it blocks hosts that would have
# worked and reassures about hosts that will not.
info "RAM ${RAM} GiB total$( [ -n "$RAM_AVAIL" ] && printf ', %s GiB available now' "$RAM_AVAIL" )"
info "swap ${SWAP:-not reported}${SWAP:+ GiB}"

if [ "$LOOGLE_INDEXED" -eq 1 ]; then
  info "this project's local Loogle index already exists — no first build ahead"
  note "at $PRE_PROJ"
else
  info "local Loogle's first index has not been built"
  note "indexing is resource-intensive and requirements vary with the pinned"
  note "Mathlib and Loogle versions"
  note "install.sh will measure the attempt and stop if the local index is not produced"
  if [ "$OS" = wsl ]; then
    note "WSL caps the VM's memory below the host's total by default; raise it in"
    note "%USERPROFILE%\\.wslconfig ([wsl2] memory=… swap=…) then 'wsl --shutdown'"
    note "from Windows, if the build is killed"
  fi
fi

# Whether a kill would be *provable* here. The cgroup v2 oom_kill counter is the
# only thing that establishes an OOM in this skill, and it does not exist in the
# root cgroup — where a plain login shell on a VM usually sits. Saying so up
# front is the difference between a test that produces evidence and one that
# produces a bare "terminated by signal 9". No verdict attached: this is about
# what can be observed, not about whether the host is adequate.
if cgroup_oom_kills >/dev/null 2>&1; then
  info "cgroup OOM counter readable — an OOM kill during the install would be recorded"
else
  info "cgroup OOM counter not readable from this shell"
  note "an OOM kill would show only as a terminating signal, which does not prove the cause"
  note "for a run where that matters, put it in its own cgroup, e.g."
  note "  systemd-run --scope bash .claude/skills/lean-kb-setup/scripts/install.sh --project <dir>"
  note "and check 'dmesg -T | grep -i oom' either way"
fi

warn "capacity for concurrent LeanExplore and local Loogle use is not predicted by this skill"
note "actual usage depends on versions, query mode, and concurrent processes"

# ------------------------------------------------------------------ disk ----

section "Disk"

PROJ_FREE="$(disk_free_gib "$PROJECT")"
HOME_FREE="$(disk_free_gib "$HOME")"
PROJ_MNT="$(disk_mount "$PROJECT")"
HOME_MNT="$(disk_mount "$HOME")"

# Reported, not judged. Download and artefact sizes move with every upstream
# publish — Mathlib's build cache, the LeanExplore corpus, the model weights —
# so a budget baked in here is a number about the day it was written.
if [ "$PROJ_MNT" = "$HOME_MNT" ]; then
  # Worth saying: one pool means the project's build artefacts and $HOME's
  # caches draw down the same free space, so the two cannot be read separately.
  info "$PROJ_MNT holds both the project and \$HOME: ${PROJ_FREE} GiB free"
  note "Mathlib's .lake, the Loogle cache, the LeanExplore corpus and the model"
  note "weights all come out of this one pool"
else
  info "project filesystem ($PROJ_MNT): ${PROJ_FREE} GiB free"
  info "\$HOME ($HOME_MNT): ${HOME_FREE} GiB free"
fi
note "install.sh downloads Mathlib's cache, the LeanExplore corpus and two models;"
note "sizes track upstream releases and are not predicted here. It will fail visibly"
note "on a full filesystem rather than being blocked by an estimate."

if [ "$OS" = wsl ] && is_windows_mount "$PROJECT"; then
  warn "project sits on a Windows drive (9p/drvfs) — Lean builds there are markedly slower"
  note "lean-lsp-mcp hard-codes a 900s loogle build timeout and a 300s index timeout,"
  note "which install.sh bypasses by building directly — but the LSP's own calls do not"
  note "consider moving or cloning the Lean project onto the WSL ext4 filesystem"
fi

# ------------------------------------------------------------- toolchain ----

section "Toolchain"

if have elan; then
  pass "elan $(elan --version 2>/dev/null | awk '{print $2}')"
elif have lake; then
  warn "lake present but elan missing — local Loogle shells out to lake and needs elan on PATH"
else
  warn "elan missing — install.sh will install it"
fi

if have uv; then
  pass "uv $(uv --version 2>/dev/null | awk '{print $2}')"
else
  warn "uv missing — install.sh will install it (userspace, no sudo)"
fi

if have rg; then
  pass "ripgrep $(rg --version 2>/dev/null | head -1 | awk '{print $2}')"
else
  cmd="$(pkg_install_cmd ripgrep)"
  warn "ripgrep missing — required by lean_local_search and lean_verify"
  if [ -n "$cmd" ]; then note "needs approval: $cmd"; else note "no known package manager; install ripgrep manually"; fi
fi

if have claude; then
  pass "claude CLI present (needed to register the MCP servers)"
else
  warn "claude CLI missing — install.sh will skip MCP registration"
fi

# --------------------------------------------------------- Lean project ----

section "Lean project"

if PROJ="$(find_lean_project "$PROJECT")"; then
  pass "found at $PROJ"
  note "toolchain: $(cat "$PROJ/lean-toolchain")"

  if [ -f "$PROJ/lakefile.toml" ]; then
    pass "lakefile.toml (install.sh can edit this automatically)"
  elif [ -f "$PROJ/lakefile.lean" ]; then
    warn "lakefile.lean — install.sh will print the require blocks instead of editing"
  else
    fail "no lakefile.toml or lakefile.lean in $PROJ"
  fi

  # Mentioning mathlib is not the same as pinning it reproducibly (KB.md).
  # Classification is done against the remote, matching install.sh exactly, so
  # preflight never green-lights a pin that install.sh will reject.
  #
  # Three outcomes, not two: exit 1 is "no such require", exit 2 is "the
  # lakefile does not parse". Folding 2 into 1 would announce that Mathlib will
  # be pinned automatically when install.sh is in fact going to refuse.
  if req="$(python3 "$HERE/introspect.py" require "$PROJ" mathlib 2>/dev/null)"; then rc=0; else rc=$?; fi

  if [ "$rc" = 2 ]; then
    fail "$PROJ/lakefile.toml does not parse — install.sh will refuse to edit it"
    note "$(printf '%s' "$req" | jget error)"
  elif [ "$rc" = 0 ]; then
    rev="$(printf '%s' "$req" | jget rev)"
    url_declared="$(printf '%s' "$req" | jget git)"
    if [ -z "$url_declared" ]; then
      fail "Mathlib require has no git URL — cannot verify what it points at"
    else
      case "$(classify_ref "$url_declared" "$rev")" in
        commit) pass "Mathlib pinned at a commit" ;;
        tag)
          tag="$(toolchain_tag "$PROJ")"
          if [ -n "$tag" ] && [ "$rev" != "$tag" ]; then
            warn "Mathlib pinned at $rev but the toolchain wants $tag — verify compatibility"
          else
            pass "Mathlib pinned at tag $rev"
          fi ;;
        head)
          fail "Mathlib required at '$rev', a branch — not reproducible"
          note "set a tag or commit in $PROJ/lakefile.toml; install.sh refuses to proceed" ;;
        unknown)
          fail "Mathlib required at '$rev', which is neither a tag nor a branch on the remote" ;;
        offline)
          warn "Mathlib pinned at '$rev' but $url_declared is unreachable — cannot verify" ;;
      esac
    fi
  elif grep -qs 'mathlib' "$PROJ/lakefile.lean" 2>/dev/null; then
    warn "Mathlib required from lakefile.lean — this skill cannot validate or edit that"
  else
    tag="$(toolchain_tag "$PROJ")"
    if [ -z "$tag" ]; then
      warn "toolchain is not a released vX.Y.Z — cannot derive a Mathlib tag automatically"
      note "pin Mathlib yourself, or switch the project to a released toolchain"
    elif git_tag_exists https://github.com/leanprover-community/mathlib4 "$tag"; then
      pass "Mathlib $tag matches the toolchain and will be pinned"
    else
      fail "no Mathlib release tag $tag for this toolchain"
      note "install.sh refuses to silently fall back to Mathlib master"
    fi
  fi

  if [ -d "$PROJ/.lake/packages/mathlib" ]; then
    pass "Mathlib already fetched"
  else
    note "Mathlib not fetched yet — expect a long first 'lake exe cache get'"
  fi
else
  fail "no lean-toolchain found at or above $PROJECT"
  note "point --project at a Lean 4 project, or create one with 'lake new'"
fi

# --------------------------------------------------------------- network ----

section "Network"

# On a connection failure curl *itself* prints 000 and then exits non-zero, so
# an `|| echo 000` fallback appends a second one and yields "000000" — which is
# not equal to "000", and every unreachable host passed. Take curl's exit
# status as the signal and use its output only when it succeeded.
#
# HEAD, not GET: `-o /dev/null` discards the body but still transfers it, and
# pypi.org/simple/ is large enough to blow an 8s budget on a healthy link. A
# host that rejects HEAD still answers with a status code, which is all this
# asks. Any answer at all means reachable — the question is connectivity.
check_host() {
  if code="$(curl -sS --head -o /dev/null -m 8 -w '%{http_code}' "$1" 2>/dev/null)"; then :; else code=000; fi
  case "$code" in
    000|"") fail "$2 unreachable ($1)" ;;
    5*)     warn "$2 answered HTTP $code — reachable but erroring" ;;
    *)      pass "$2 reachable (HTTP $code)" ;;
  esac
}

check_host https://github.com                                        "GitHub (Mathlib, repl, loogle)"
check_host https://pypi.org/simple/                                  "PyPI (lean-lsp-mcp, lean-explore)"
check_host https://astral.sh                                         "astral.sh (uv installer)"
check_host https://huggingface.co                                    "HuggingFace (Qwen3 embedding/reranker)"
check_host https://pub-48b75babc4664808b15520033423c765.r2.dev/manifest.json "LeanExplore data (Cloudflare R2)"

summary "Preflight"
