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

# Total physical RAM in GiB, one decimal place.
ram_gib() {
  case "$(uname -s)" in
    Linux)  awk '/^MemTotal:/ { printf "%.1f", $2 / 1048576 }' /proc/meminfo ;;
    Darwin) sysctl -n hw.memsize | awk '{ printf "%.1f", $1 / 1073741824 }' ;;
    *)      echo 0 ;;
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
SKILL_VERSION="0.7.1"
LEAN_LSP_MCP_VERSION="${LEAN_LSP_MCP_VERSION:-0.29.0}"
LEAN_EXPLORE_VERSION="${LEAN_EXPLORE_VERSION:-1.2.1}"

# Space requirements in GiB, from measured artefact sizes. See reference.md.
NEED_DISK_PROJECT=12      # Mathlib + deps + repl in the project's .lake
NEED_DISK_HOME=14         # loogle ~2 + LeanExplore data 3.9 + HF models 2.5
                          # + tool venvs ~1.5-3.5 + one Lean toolchain ~2.8

# RAM in GiB, as three bands. Loogle's first Mathlib index is the peak consumer
# of the whole stack; upstream measures ~13 GiB peak RSS, ~7 GiB on warm loads.
NEED_RAM_HARD=6           # below this nothing works reliably
NEED_RAM_COMFORT=8        # below this `import Mathlib` and LeanExplore swap
NEED_RAM_LOOGLE_INDEX=14  # below this the initial loogle index OOMs

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

# ------------------------------------------------------------ lake jobs ----
#
# Lake defaults to one worker per core. That is fine while `lake exe cache get`
# hits — unpacking oleans is I/O — but when the cache misses, Mathlib compiles
# from source and each worker is a full `lean` process holding its imports in
# memory. On a high-core, memory-constrained host the default reliably invites
# the OOM killer, which surfaces as an opaque mid-build failure.

RAM_PER_LAKE_JOB=2        # GiB peak per `lean` worker compiling Mathlib
RAM_LAKE_RESERVED=2       # GiB left for the OS, the editor, and the LSP

# Cores, capped by what RAM can actually feed. Never below 1.
lake_jobs_default() {
  awk -v ram="$(ram_gib)" -v cpus="$(cpu_count)" \
      -v per="$RAM_PER_LAKE_JOB" -v res="$RAM_LAKE_RESERVED" '
    BEGIN {
      n = int((ram - res) / per)
      if (n > cpus) n = cpus
      if (n < 1) n = 1
      print n
    }'
}
