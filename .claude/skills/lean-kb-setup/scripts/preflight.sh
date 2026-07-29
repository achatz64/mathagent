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
CPUS="$(cpu_count)"

# Resolved here rather than in the "Lean project" section further down, because
# the memory verdict depends on it: the 14 GiB figure is the cost of *building*
# the Loogle index, and a host that already has one is not going to pay it
# again. Reporting a permanent blocker for a one-off cost turns every repair run
# and every `--only register` on a working install into a failure.
#
# Both are "no" answers, not errors: a run with no project yet, or with no index
# yet, is exactly the case where the build peak does still apply.
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

section "Memory (${RAM} GiB total)"

if lt "$RAM" "$NEED_RAM_HARD"; then
  fail "under ${NEED_RAM_HARD} GiB — building Mathlib and running the LSP will thrash"
elif lt "$RAM" "$NEED_RAM_COMFORT"; then
  warn "under ${NEED_RAM_COMFORT} GiB — 'import Mathlib' and LeanExplore search will be tight"
  note "both fit, but expect swapping; close other memory-hungry processes"
elif lt "$RAM" "$NEED_RAM_RUNTIME"; then
  # The measured workload is ~9 GiB resident for the two servers together. That
  # is not the same as a 9 GiB host: on one, those 9 GiB are the whole machine,
  # with nothing left for the kernel, Claude Code, an editor or a build. So the
  # host figure carries headroom, and the two numbers are reported separately
  # rather than one standing in for the other.
  warn "under ${NEED_RAM_RUNTIME} GiB — both MCP servers measured ~${RAM_BOTH_SERVERS_RSS} GiB resident together"
  note "plus ~${RAM_HOST_HEADROOM} GiB for the OS, Claude Code and an editor"
  note "each server works alone; running both alongside real work will swap"
else
  pass "enough for both MCP servers (~${RAM_BOTH_SERVERS_RSS} GiB measured) plus ~${RAM_HOST_HEADROOM} GiB headroom"
fi

if [ "$LOOGLE_INDEXED" -eq 1 ]; then
  # The expensive part is already paid for. What is left is loading an index
  # that exists, which is a different and much smaller number.
  if lt "$RAM" "$NEED_RAM_LOOGLE_WARM"; then
    fail "under ${NEED_RAM_LOOGLE_WARM} GiB — loading the existing Loogle index needs ~7 GiB"
  else
    pass "this project's Loogle index already exists; the ${NEED_RAM_LOOGLE_INDEX} GiB build peak does not apply"
    note "only a first index for a (project, toolchain) pays that; $PRE_PROJ has one"
  fi
elif lt "$RAM" "$NEED_RAM_LOOGLE_INDEX"; then
  # A blocker, not a degradation: the loogle stage is a hard stop on a missing
  # index, so a default install.sh run will abort here rather than quietly
  # settling for the remote API.
  fail "under ${NEED_RAM_LOOGLE_INDEX} GiB — local Loogle's first Mathlib index needs ~13 GiB peak RSS"
  note "it will OOM, and the loogle stage stops the install rather than falling back"
  note "either raise available RAM, or run install.sh --skip loogle to accept the remote API"
  if [ "$OS" = wsl ]; then
    note "WSL caps at ~50% of host RAM by default; raise it in %USERPROFILE%\\.wslconfig:"
    note "  [wsl2]"
    note "  memory=14GB"
    note "  swap=8GB"
    note "then run 'wsl --shutdown' from Windows. See reference.md."
  else
    note "install.sh --skip loogle keeps everything else local; see reference.md"
  fi
else
  pass "enough for local Loogle's initial Mathlib index"
fi

# ------------------------------------------------------------------ disk ----

section "Disk"

PROJ_FREE="$(disk_free_gib "$PROJECT")"
HOME_FREE="$(disk_free_gib "$HOME")"
PROJ_MNT="$(disk_mount "$PROJECT")"
HOME_MNT="$(disk_mount "$HOME")"

if [ "$PROJ_MNT" = "$HOME_MNT" ]; then
  # One pool, so the two budgets compete for the same bytes. Checking them
  # separately would pass 15 GiB free against a 12 and a 14 GiB requirement.
  NEED_BOTH=$((NEED_DISK_PROJECT + NEED_DISK_HOME))
  if lt "$PROJ_FREE" "$NEED_BOTH"; then
    fail "project and \$HOME share $PROJ_MNT with ${PROJ_FREE} GiB free, needs ~${NEED_BOTH} GiB combined"
    note "Mathlib ~${NEED_DISK_PROJECT} GiB in the project, ~${NEED_DISK_HOME} GiB of caches and models in \$HOME"
  else
    pass "$PROJ_MNT (project and \$HOME): ${PROJ_FREE} GiB free, needs ~${NEED_BOTH} GiB"
  fi
else
  if lt "$PROJ_FREE" "$NEED_DISK_PROJECT"; then
    fail "project filesystem has ${PROJ_FREE} GiB free, needs ~${NEED_DISK_PROJECT} GiB for Mathlib"
  else
    pass "project filesystem ($PROJ_MNT): ${PROJ_FREE} GiB free"
  fi

  if lt "$HOME_FREE" "$NEED_DISK_HOME"; then
    fail "\$HOME has ${HOME_FREE} GiB free, needs ~${NEED_DISK_HOME} GiB"
    note "LeanExplore data 3.9, HF models 2.5, loogle ~2, venvs 1.5-3.5, Lean toolchain ~2.8 GiB"
  else
    pass "\$HOME ($HOME_MNT): ${HOME_FREE} GiB free"
  fi
fi

if [ "$OS" = wsl ] && is_windows_mount "$PROJECT"; then
  warn "project sits on a Windows drive (9p/drvfs) — Lean builds there are 5-10x slower"
  note "lean-lsp-mcp hard-codes a 900s loogle build timeout and a 300s index timeout"
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
