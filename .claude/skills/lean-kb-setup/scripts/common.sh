#!/usr/bin/env bash
# Shared helpers for the lean-kb-setup skill. Sourced, never executed directly.
# Targets: Linux, macOS, WSL2. Bash 3.2+ (macOS ships 3.2), POSIX-ish tools only.

# ---------------------------------------------------------------- output ----

if [ -t 1 ]; then
  C_B=$'\033[1m'; C_R=$'\033[31m'; C_Y=$'\033[33m'; C_G=$'\033[32m'; C_D=$'\033[2m'; C_N=$'\033[0m'
else
  C_B=; C_R=; C_Y=; C_G=; C_D=; C_N=
fi

# Counters consumed by the final summary of preflight/verify.
COUNT_OK=0; COUNT_WARN=0; COUNT_FAIL=0

section() { printf '\n%s\n' "${C_B}$*${C_N}"; }
pass()    { COUNT_OK=$((COUNT_OK + 1));     printf '  %sPASS%s  %s\n' "$C_G" "$C_N" "$*"; }
warn()    { COUNT_WARN=$((COUNT_WARN + 1)); printf '  %sWARN%s  %s\n' "$C_Y" "$C_N" "$*"; }
fail()    { COUNT_FAIL=$((COUNT_FAIL + 1)); printf '  %sFAIL%s  %s\n' "$C_R" "$C_N" "$*"; }
note()    { printf '        %s%s%s\n' "$C_D" "$*" "$C_N"; }
# An observation the reader needs, with no verdict attached. Counted nowhere:
# it is neither a check that passed nor one that failed, and a script that
# reports a host fact it refuses to draw a conclusion from must not have that
# show up as either.
info()    { printf '  %sINFO%s  %s\n' "$C_B" "$C_N" "$*"; }
step()    { printf '\n%s==>%s %s\n' "$C_B" "$C_N" "$*"; }
die()     { printf '\n%sfatal:%s %s\n' "$C_R" "$C_N" "$*" >&2; exit 1; }

summary() {
  printf '\n%s%s: %d passed, %d warnings, %d failures%s\n' \
    "$C_B" "${1:-summary}" "$COUNT_OK" "$COUNT_WARN" "$COUNT_FAIL" "$C_N"
  [ "$COUNT_FAIL" -eq 0 ]
}

have() { command -v "$1" >/dev/null 2>&1; }

# Read one field from a JSON object on stdin. Absent/null prints empty.
# Used instead of ad-hoc grep/sed so values containing quotes or newlines
# cannot corrupt the caller.
jget() {
  python3 -c 'import json,sys
try: d = json.load(sys.stdin)
except ValueError: sys.exit(1)
v = d.get(sys.argv[1])
print("" if v is None else v)' "$1"
}

# ------------------------------------------------------------ host probes ----

# linux | wsl | macos | unsupported. WSL is reported separately from linux
# because it constrains RAM and because /mnt/* paths are a performance trap.
os_kind() {
  case "$(uname -s)" in
    Linux)
      if grep -qi 'microsoft\|wsl' /proc/sys/kernel/osrelease 2>/dev/null; then
        echo wsl
      else
        echo linux
      fi
      ;;
    Darwin) echo macos ;;
    *)      echo unsupported ;;
  esac
}

# Live host facts, for reporting. Nothing in this skill compares them against a
# threshold — see the note above the version pins.

# Total physical RAM in GiB, one decimal place.
ram_gib() {
  case "$(uname -s)" in
    Linux)  awk '/^MemTotal:/ { printf "%.1f", $2 / 1048576 }' /proc/meminfo ;;
    Darwin) sysctl -n hw.memsize | awk '{ printf "%.1f", $1 / 1073741824 }' ;;
    *)      echo 0 ;;
  esac
}

# Currently available RAM in GiB — what the kernel thinks is reclaimable now,
# which is a different and more useful number than the total. Empty when the
# host does not report it.
ram_available_gib() {
  case "$(uname -s)" in
    Linux)  awk '/^MemAvailable:/ { printf "%.1f", $2 / 1048576; found = 1 }
                 END { exit !found }' /proc/meminfo ;;
    Darwin) _pg="$(sysctl -n hw.pagesize 2>/dev/null)" || return 1
            vm_stat 2>/dev/null | awk -v pg="$_pg" '
              /Pages free/       { f = $3 }
              /Pages inactive/   { i = $3 }
              END { if (pg == "" ) exit 1; gsub(/\./, "", f); gsub(/\./, "", i)
                    printf "%.1f", (f + i) * pg / 1073741824 }' ;;
    *)      return 1 ;;
  esac
}

# Total swap in GiB. Empty when there is none or the host does not report it.
swap_gib() {
  case "$(uname -s)" in
    Linux)  awk '/^SwapTotal:/ { printf "%.1f", $2 / 1048576; found = 1 }
                 END { exit !found }' /proc/meminfo ;;
    Darwin) sysctl -n vm.swapusage 2>/dev/null \
              | sed -n 's/.*total = \([0-9.]*\)M.*/\1/p' \
              | awk 'NF { printf "%.1f", $1 / 1024 }' ;;
    *)      return 1 ;;
  esac
}

cpu_count() {
  if have nproc; then nproc
  elif have sysctl; then sysctl -n hw.ncpu
  else echo 1
  fi
}

# Free space in GiB on the filesystem holding $1, walking up to the nearest
# existing ancestor so it works for paths that have not been created yet.
disk_free_gib() {
  _p="$1"
  while [ ! -e "$_p" ] && [ "$_p" != "/" ]; do _p="$(dirname "$_p")"; done
  df -Pk "$_p" 2>/dev/null | awk 'NR == 2 { printf "%.1f", $4 / 1048576 }'
}

# Mount point holding $1. Two paths on the same mount share one free-space
# pool, so their requirements have to be added rather than checked separately.
disk_mount() {
  _p="$1"
  while [ ! -e "$_p" ] && [ "$_p" != "/" ]; do _p="$(dirname "$_p")"; done
  df -Pk "$_p" 2>/dev/null | awk 'NR == 2 { print $NF }'
}

# Float comparison: is $1 < $2?
lt() { awk -v a="$1" -v b="$2" 'BEGIN { exit !(a < b) }'; }

# Running total of OOM kills in this process's cgroup (v2 only). Non-zero exit
# when the host cannot answer, which is not the same as an answer of zero — a
# caller comparing before and after must treat "empty" as "no evidence either
# way" rather than as "nothing was killed".
#
# What a positive delta establishes: *something in this cgroup* was OOM-killed
# while the measurement was running. It does not identify the victim. The
# measured subprocess is the likeliest one when it also died, but any other
# process sharing the cgroup — a sibling, the shell, an editor under the same
# scope — increments the same counter. Report it as an OOM kill in this cgroup,
# not as proof that this command was the one killed.
cgroup_oom_kills() {
  _rel="$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup 2>/dev/null)"
  [ -n "$_rel" ] || return 1
  _f="/sys/fs/cgroup${_rel}/memory.events"
  [ -r "$_f" ] || return 1
  awk '$1 == "oom_kill" { print $2; found = 1 } END { exit !found }' "$_f"
}

# True when $1 sits on a Windows drive mounted into WSL (9p/drvfs). Lean builds
# there are slow enough to trip lean-lsp-mcp's fixed 900s/300s timeouts.
is_windows_mount() {
  case "$(cd "$(dirname "$1")" 2>/dev/null && pwd -P || echo "$1")" in
    /mnt/[a-z]/*|/mnt/[a-z]) return 0 ;;
    *) return 1 ;;
  esac
}

# ------------------------------------------------------- package managers ----

pkg_manager() {
  for m in brew apt-get dnf pacman zypper apk; do
    have "$m" && { echo "$m"; return; }
  done
  echo none
}

# The exact command a human should run to install $1. Printed, never executed
# without --allow-sudo, because these need root on every platform but macOS.
pkg_install_cmd() {
  case "$(pkg_manager)" in
    brew)    echo "brew install $1" ;;
    apt-get) echo "sudo apt-get update && sudo apt-get install -y $1" ;;
    dnf)     echo "sudo dnf install -y $1" ;;
    pacman)  echo "sudo pacman -S --noconfirm $1" ;;
    zypper)  echo "sudo zypper install -y $1" ;;
    apk)     echo "sudo apk add $1" ;;
    *)       echo "" ;;
  esac
}

# ------------------------------------------------------- the Lean project ----

# Walk up from $1 looking for a lean-toolchain, the one file every Lean 4
# project has and the file lean-lsp-mcp keys its loogle build off.
find_lean_project() {
  _d="$(cd "$1" 2>/dev/null && pwd -P)" || return 1
  while [ -n "$_d" ] && [ "$_d" != "/" ]; do
    [ -f "$_d/lean-toolchain" ] && { echo "$_d"; return 0; }
    _d="$(dirname "$_d")"
  done
  return 1
}

# leanprover/lean4:v4.31.0 -> v4.31.0. Empty for nightlies and other formats
# that have no matching Mathlib release tag. Strips CR first: a repo checked out
# on Windows leaves CRLF endings that would defeat the end anchor.
toolchain_tag() {
  tr -d '\r' <"$1/lean-toolchain" 2>/dev/null \
    | sed -n 's|.*:\(v[0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\)$|\1|p'
}

git_tag_exists() {
  git ls-remote --tags --exit-code "$1" "refs/tags/$2" >/dev/null 2>&1
}

is_commit_sha() { printf '%s' "$1" | grep -Eq '^[0-9a-f]{40}$'; }

# Classify a require's revision against the actual remote: commit | tag | head
# | unknown | offline.
#
# Positive validation, not a blacklist of branch names — `develop`, `stable`,
# and `release-next` are every bit as moving as `master`, and no fixed list
# catches them. A single ls-remote answers both questions at once.
classify_ref() { # url, rev
  if is_commit_sha "$2"; then echo commit; return; fi
  if ! _refs="$(git ls-remote "$1" "refs/heads/$2" "refs/tags/$2" 2>/dev/null)"; then
    echo offline; return
  fi
  case "$_refs" in
    *"refs/heads/$2"*) echo head ;;
    *"refs/tags/$2"*)  echo tag ;;
    *)                 echo unknown ;;
  esac
}

# -------------------------------------------------------------- versions ----
#
# Pins live here so the manifest written by install.sh and the checks in
# preflight.sh/verify.sh can never disagree about what "installed" means.

# 0.9.2: the Qwen3 reranker is prefetched during installation by default
#        (`--no-rerank-prefetch` opts out), because nothing in the registration
#        can stop a runtime call from reranking: `mcp serve` takes only
#        --backend/--api-key and 1.2.1 reads no env var or config key for it.
#        Prefetching moves the download out of a live tool call. The call site is
#        the only real lever, so the rule "pass rerank_top explicitly, default 0"
#        lives in the project's CLAUDE.md. verify reports whether the model is on
#        disk.
# 0.9.1: measurements are append-only, self-contained attempt records — each
#        carries its own stage, timestamp, outcome, host facts, pins and metrics,
#        so a later run cannot re-attribute an older figure to a new host. Exit
#        status and terminating signal are recorded, for failed attempts too, and
#        an unreadable OOM counter is distinguished from an observed zero. The
#        LeanExplore smoke calls pass rerank_top=0; exercising the reranker is a
#        separate, explicit contract (`--rerank-check` / `--rerank`). A Loogle
#        run that exits non-zero must prove the index loads and answers before
#        the stage passes — an existing file is no longer evidence on its own.
# 0.9.0: no resource estimates anywhere. Every RAM, disk, download-size and
#        timing constant is gone, and nothing derives a PASS/WARN/FAIL from one.
#        preflight reports live host facts as INFO; install.sh measures the
#        expensive steps (elapsed, peak RSS, signal, cgroup OOM, artefact size)
#        and records them in the manifest as provenance, never as requirements.
# 0.8.1: `measured` no longer re-enables errexit, which killed the script at the
#        call site before the failure diagnostics could run; the registration
#        pins LEAN_LOOGLE_CACHE_DIR as well as PATH; verify reads the
#        toolchain-keyed loogle binary; a signal alone is no longer reported as a
#        confirmed OOM; the loogle checkout and the LeanExplore data are
#        classified `shared`.
# 0.8.0: first-VM-run fixes. `lake -j` never existed in Lake 5.0, so the whole
#        job cap is gone; the Loogle clone/build/index runs directly instead of
#        through the tool call that wraps it in upstream's 900s/300s timeouts;
#        registrations carry the PATH the server will actually be spawned with;
#        verify compares the resolved executable and the ordered argv, and runs
#        the server from its own registration.
# 0.7.1: JSON null counts as malformed, not absent; verify validates the whole
#        entry (command, args, project path, backend) for both servers; a failed
#        rollback keeps its in-flight provenance marker.
# 0.7.0: a malformed MCP config is "unknown", never "absent" — and registering
#        is refused when the rollback snapshot is unreadable; the Loogle
#        registration checks are exact fields, not substrings of a printed
#        string; verify's --skip reaches the binary probes.
# 0.6.0: verify probes Loogle with the dead endpoint and demands the exact pin;
#        MCP rollback is per-entry, not per-file; manifest never seeds version
#        keys for stages that did not complete.
# 0.5.0: Loogle fail-closed at registration and runtime too (LOOGLE_URL pin);
#        install.sh exits non-zero on any incomplete stage.
# 0.4.0: local Loogle is all-or-nothing — no silent remote fallback.
# 0.3.0: provenance carries a sticky origin; lake build is capped by RAM.
# 0.2.x manifests hold flat provenance strings; the action vocabulary did not
# change, so _merge_provenance normalises them and derives the origin in place.
SKILL_VERSION="0.9.2"
LEAN_LSP_MCP_VERSION="${LEAN_LSP_MCP_VERSION:-0.29.0}"
LEAN_EXPLORE_VERSION="${LEAN_EXPLORE_VERSION:-1.2.1}"

# ------------------------------------------ no resource estimates, at all ----
#
# There are deliberately no memory, disk, download-size or timing constants
# here, and nothing in this skill decides anything from one.
#
# Every figure that used to live here was a measurement of one workload, on one
# host, at one set of pinned versions. What the Loogle index costs moves with
# the Mathlib revision it indexes; what LeanExplore costs moves with its
# release, its model implementation and the query parameters; artefact and
# download sizes move with every upstream publish; timings move with all of that
# plus the disk and the network. None of it changes when this skill changes, so
# a constant frozen from one run is a claim about every future run that nobody
# re-checks — and its failure mode is the bad one: it blocks an install on a
# host that would have worked, or promises "enough" for one that will not.
#
# So the skill measures instead of predicting. `install.sh` runs the expensive
# step and reports what that execution produced — exit status, terminating
# signal, elapsed time, peak RSS where the host can report it, cgroup OOM
# events, the artefact's actual size — and stops if the artefact is not there.
# `preflight.sh` reports live host facts and draws no verdict from them. An OOM
# is asserted only from an OOM counter, never from a total or a signal.
#
# What stays: version pins, commit hashes, exit-code contracts, protocol
# values, and deliberate policy limits like LOOGLE_NULL_BACKEND. Those are
# reproducibility inputs and behavioural contracts, not estimates.
#
# Historical measurements belong in dated test reports, not in executable
# policy. Per-run measurements belong in the manifest, as provenance.

# Closing lean-lsp-mcp's runtime fallback to the public Loogle API.
#
# `lean_loogle` tries the local index, and on ANY exception logs "falling back
# to remote" and answers from loogle.lean-lang.org instead. There is no strict
# switch upstream. But `LOOGLE_URL` is its documented knob for pointing the
# remote backend elsewhere, so pointing it at a closed port turns that silent
# degradation into a visible connection error.
#
# Set only when the local index exists. `--skip loogle` means the user asked
# for the remote API, and then this must not be applied.
LOOGLE_NULL_BACKEND="http://127.0.0.1:1"

# --------------------------------------------------- the registered PATH ----
#
# Claude Code launches MCP servers directly, not through a login shell, so the
# server inherits whatever environment Claude itself was started with. That is
# routinely a PATH without ~/.elan/bin — and lean-lsp-mcp shells out to `lake`
# and `git` to build and run local Loogle. The install-time checks all pass,
# because the installer put elan on its own PATH; the server then fails at the
# first query after a restart, which is exactly the split this exists to close.
#
# So the PATH the server will get is written into the registration rather than
# assumed. Absolute directories only: a relative entry resolves against whatever
# working directory Claude happens to spawn the server in.
mcp_runtime_path() {
  python3 - "$HOME/.elan/bin" "$HOME/.local/bin" <<'PY'
import os, sys

# The tool directories first, then everything this installer inherited, so the
# compilers, git and the system utilities a Lean build needs are all still
# reachable. Never a hardcoded /root or /home/<name>: $HOME is the only
# portable answer, and this runs as whoever installed.
seen, out = set(), []
for d in list(sys.argv[1:]) + os.environ.get("PATH", "").split(os.pathsep):
    if not d or not os.path.isabs(d) or d in seen:
        continue
    seen.add(d)
    out.append(d)
print(os.pathsep.join(out))
PY
}
