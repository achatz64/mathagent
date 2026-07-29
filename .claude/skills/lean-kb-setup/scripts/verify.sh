#!/usr/bin/env bash
# Test the installed stack end to end: binaries, Mathlib, both MCP servers, and
# a real query through each local index.
#
# Usage: verify.sh [--project DIR] [--quick] [--skip STAGES]
#                  [--mcp-scope project|local|user]
#
#   --quick  import one small Mathlib module instead of all of Mathlib, and
#            skip the Loogle query (which loads ~7 GiB of oleans)
#
# Exit 0 when nothing failed.
#
# A missing local Loogle index is a FAIL, not a warning. It still "works" —
# lean_loogle answers from the remote API — which is exactly why it has to be
# loud: a silent downgrade to a rate-limited remote service is the failure mode
# this whole check exists for. Use --skip loogle to opt out deliberately.

set -uo pipefail   # deliberately no -e: every check must run and be reported
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/common.sh"

PROJECT="$PWD"; QUICK=0; SKIP=""; MCP_SCOPE="project"
while [ $# -gt 0 ]; do
  case "$1" in
    --project) PROJECT="$2"; shift 2 ;;
    --quick)   QUICK=1; shift ;;
    --skip)    SKIP="$2"; shift 2 ;;
    --mcp-scope) MCP_SCOPE="$2"; shift 2 ;;
    -h|--help) sed -n '2,16p' "$0"; exit 0 ;;
    *) die "unknown argument: $1" ;;
  esac
done

# Sections --skip can actually suppress. Validated, so an ineffective value is
# an error rather than a silent no-op.
SKIPPABLE="mathlib leanlsp loogle leanexplore register"
for s in $SKIP; do
  case " $SKIPPABLE " in
    *" $s "*) ;;
    *) die "cannot skip '$s' — skippable sections: $SKIPPABLE" ;;
  esac
done

case "$MCP_SCOPE" in
  project|local|user) ;;
  *) die "invalid --mcp-scope '$MCP_SCOPE' — use project, local, or user" ;;
esac

skipped() { case " $SKIP " in *" $1 "*) return 0 ;; esac; return 1; }

export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
PROJ="$(find_lean_project "$PROJECT")" || die "no Lean project at or above $PROJECT"

# ------------------------------------------------------------- binaries ----

section "Binaries"

# Version probes get a hard timeout. `lake --version` in particular can block
# for minutes: outside a Lean project elan resolves a *default* toolchain and
# will download one if none is installed.
#
# Probes run as argument vectors, never through `sh -c` with an interpolated
# project path — a path containing an apostrophe would otherwise break or
# inject shell syntax.
probe() { if have timeout; then timeout 60 "$@"; else "$@"; fi; }

check_bin() { # binary, required|optional, then the version argv
  bin="$1"; requirement="$2"; shift 2
  if ! have "$bin"; then
    if [ "$requirement" = required ]; then fail "$bin not on PATH"; else warn "$bin not on PATH"; fi
    return
  fi
  # A probe that exits non-zero is a broken install, not a pass.
  if out="$(probe "$@" 2>/dev/null)"; then
    pass "$bin $(printf '%s' "$out" | head -1)"
  else
    fail "$bin is on PATH but '$*' failed"
  fi
}

# A binary belongs to the section that installs it, so --skip has to reach it
# too. Otherwise a staged install — Mathlib first, tools afterwards — can never
# report success: `verify.sh --skip leanlsp` would still FAIL on a lean-lsp-mcp
# that is absent exactly as instructed. uv, ripgrep and lake are prerequisites
# of the whole stack, not of one section, so they stay unconditional.
check_bin_for() { # section, binary, required|optional, then the version argv
  _sec="$1"; shift
  if skipped "$_sec"; then note "$1 not checked (--skip $_sec)"; return; fi
  check_bin "$@"
}

check_bin uv required uv --version
check_bin rg required rg --version
check_bin_for leanlsp     lean-lsp-mcp required lean-lsp-mcp --version
check_bin_for leanexplore lean-explore optional lean-explore --version

# lake runs from inside the project so elan uses its pinned toolchain. The cd
# happens in bash, so the path is never re-parsed by a shell.
if have lake; then
  if out="$( (cd "$PROJ" && probe lake --version) 2>/dev/null )"; then
    pass "lake $(printf '%s' "$out" | head -1)"
  else
    fail "lake is on PATH but 'lake --version' failed in $PROJ"
  fi
else
  fail "lake not on PATH"
fi

# -------------------------------------------------------------- Mathlib ----

if skipped mathlib; then
  section "Mathlib"
  note "skipped"
else
section "Mathlib"

if [ -d "$PROJ/.lake/packages/mathlib" ]; then
  pass "fetched into $PROJ/.lake/packages/mathlib"

  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  if [ "$QUICK" -eq 1 ]; then
    printf 'import Mathlib.Logic.Basic\nexample : True := trivial\n' >"$tmp/Probe.lean"
    what="Mathlib.Logic.Basic"
  else
    printf 'import Mathlib\nexample : True := trivial\n' >"$tmp/Probe.lean"
    what="all of Mathlib"
  fi

  if out="$( (cd "$PROJ" && lake env lean "$tmp/Probe.lean") 2>&1 )"; then
    pass "$what imports and elaborates"
  else
    fail "importing $what failed"
    note "$(printf '%s' "$out" | head -5)"
  fi
else
  fail "Mathlib not fetched — run install.sh --only mathlib"
fi

if [ -d "$PROJ/.lake/packages/repl" ] || [ -d "$PROJ/.lake/packages/REPL" ]; then
  pass "Lean REPL present (fast lean_run_code / lean_multi_attempt)"
else
  warn "Lean REPL absent — those tools fall back to the slower LSP path"
fi

fi

# --------------------------------------------------------- lean-lsp-mcp ----

if skipped leanlsp; then
  section "lean-lsp MCP server"
  note "skipped"
else
section "lean-lsp MCP server"

LSP_CORE="lean_goal,lean_diagnostic_messages,lean_hover_info,lean_local_search,lean_loogle,lean_build"

if have lean-lsp-mcp; then
  if out="$(python3 "$HERE/mcp_smoke.py" --timeout 300 --expect-tools "$LSP_CORE" \
              -- lean-lsp-mcp --lean-project-path "$PROJ" 2>&1)"; then
    pass "handshake ok, core tools present"
    note "$(printf '%s' "$out" | sed -n '2p' | cut -c1-160)"
  else
    fail "handshake or tools/list failed"
    note "$(printf '%s' "$out" | tail -3)"
  fi

  # Proves ripgrep wiring and project resolution, not just that the server boots.
  if out="$(python3 "$HERE/mcp_smoke.py" --timeout 300 --quiet \
              --call lean_local_search --args '{"query": "Nat.add_comm", "limit": 3}' \
              -- lean-lsp-mcp --lean-project-path "$PROJ" 2>&1)"; then
    pass "lean_local_search returned matches"
  else
    fail "lean_local_search failed (ripgrep missing, or Mathlib not built)"
    note "$(printf '%s' "$out" | tail -3)"
  fi
else
  fail "lean-lsp-mcp not installed"
fi

fi

# --------------------------------------------------------- local Loogle ----

if skipped loogle; then
  section "Local Loogle index"
  note "skipped"
else
section "Local Loogle index"

cache="${LEAN_LOOGLE_CACHE_DIR:-$HOME/.cache/lean-lsp-mcp/loogle}"
bin="$(ls -1 "$cache"/repo-*/.lake/build/bin/loogle 2>/dev/null | head -1)"

# The index is keyed on sha256 of the resolved project path, so any *.idx in
# the shared cache may belong to a different project. Ask for this project's.
#
# `loogle-index` exits 0 whether or not the file is there — computing a path is
# a different question from whether it exists — so the answer is in "exists".
# Reading the exit status instead would report every missing index as present.
idx=""; expected=""
if idx_json="$(python3 "$HERE/introspect.py" loogle-index "$PROJ" --cache-dir "$cache" 2>/dev/null)"; then
  expected="$(printf '%s' "$idx_json" | jget path)"
  if [ "$(printf '%s' "$idx_json" | jget exists)" = "True" ]; then idx="$expected"; fi
else
  warn "could not compute the loogle index path for this project"
fi

if [ -n "$bin" ]; then pass "binary built: $bin"; else fail "no local loogle binary"; fi

if [ -n "$idx" ]; then
  pass "index for THIS project present: $(du -h "$idx" | awk '{print $1}')"
elif [ -n "$bin" ]; then
  fail "binary built but this project has no index — first indexing run likely OOMed"
  note "expected at ${expected:-$cache/index/mathlib-<project-hash>.idx}"
  note "lean_loogle is silently answering from the remote API (3 req/30s)"
  other="$(ls -1 "$cache"/index/*.idx 2>/dev/null | wc -l | tr -d ' ')"
  [ "$other" != "0" ] && note "$other index file(s) exist for other projects; they do not apply here"
else
  fail "local Loogle not installed — lean_loogle is using the remote API (3 req/30s)"
  note "run install.sh --only loogle, or verify.sh --skip loogle to opt out deliberately"
fi

if [ -n "$idx" ] && [ "$QUICK" -eq 0 ] && ! skipped loogle; then
  # LOOGLE_URL is pinned to the dead endpoint for the probe too. Without it,
  # an index that exists but cannot be loaded makes upstream catch the local
  # exception and answer from loogle.lean-lang.org — and this check prints PASS
  # for a query that never touched the local index. The file existing is not
  # evidence that it loads.
  if out="$(LEAN_LOOGLE_LOCAL=true LOOGLE_URL="$LOOGLE_NULL_BACKEND" \
            python3 "$HERE/mcp_smoke.py" --timeout 600 --quiet \
              --call lean_loogle --args '{"query": "Nat.add_comm", "num_results": 3}' \
              -- lean-lsp-mcp --lean-project-path "$PROJ" --loogle-local 2>&1)"; then
    pass "lean_loogle answered from the local index (remote endpoint was dead)"
  else
    fail "lean_loogle query failed despite the index being present"
    note "$(printf '%s' "$out" | tail -3)"
  fi
fi

fi

# --------------------------------------------------------- lean-explore ----

if skipped leanexplore; then
  section "LeanExplore local index"
  note "skipped"
else
section "LeanExplore local index"

active="$HOME/.lean_explore/active_version"
if [ -f "$active" ] && [ -f "$HOME/.lean_explore/cache/$(cat "$active")/lean_explore.db" ]; then
  v="$(cat "$active")"
  pass "data toolchain $v ($(du -sh "$HOME/.lean_explore/cache/$v" | awk '{print $1}'))"
else
  fail "no local data — run install.sh --only leanexplore"
fi

if have lean-explore; then
  # Deliberately NOT `lean-explore search`: that subcommand builds an ApiClient
  # and needs LEANEXPLORE_API_KEY, so it would test the hosted API — the exact
  # backend this install is meant to avoid. The local backend is only reachable
  # through the MCP server.
  LE_CORE="search,search_summary,get_source_code,get_docstring,get_dependencies"
  if out="$(python3 "$HERE/mcp_smoke.py" --timeout 600 --quiet --expect-tools "$LE_CORE" \
              --call search_summary --args '{"query": "commutativity of addition", "limit": 3}' \
              -- lean-explore mcp serve --backend local 2>&1)"; then
    pass "MCP server answered a semantic query from the local backend"
  else
    fail "lean-explore MCP server failed"
    note "$(printf '%s' "$out" | tail -3)"
  fi
else
  fail "lean-explore not installed"
fi

fi

# ------------------------------------------------------------- Claude CC ----

if skipped register; then
  section "Claude Code registration"
  note "skipped"
else
section "Claude Code registration"

# Scope-exact, and it reads *how* each server was registered. `claude mcp list`
# resolves across scopes and says nothing about arguments, so it would report a
# PASS for a lean-lsp registered without --loogle-local — a working server
# quietly pointed at the remote Loogle API, which is the thing being tested.
ROOT="$(git -C "$PROJ" rev-parse --show-toplevel 2>/dev/null || echo "$PROJ")"

# Every fact comes back as a structured field. The `args`/`env` strings the same
# call returns are flattened with spaces and `=`, so substring tests on them are
# not the exact checks they look like: NOTE=LOOGLE_URL=<pin> satisfies a search
# for the pin while LOOGLE_URL itself is unset, <pin> is a prefix of a different
# port, and `--loogle-local=false` contains `--loogle-local`. Each of those is a
# live remote fallback that would be reported as PASS.
#
# `info` is left set for the caller, which reads the per-server fields it asked
# for. PASS is printed only once *everything* structural holds — announcing "it
# is registered" before validating the entry is how an unreadable or wrongly
# built registration slips through a run that then exits 0.
check_registration() { # name, expected binary, then extra introspect flags
  _name="$1"; _bin="$2"; shift 2
  info="$(python3 "$HERE/introspect.py" mcp-registered "$_name" \
            --scope "$MCP_SCOPE" --repo-root "$ROOT" "$@" 2>/dev/null)"

  case "$(printf '%s' "$info" | jget registered)" in
    True) ;;
    False) fail "$_name not registered in $MCP_SCOPE scope — run install.sh --only register"
           return 1 ;;
    # Not a warning: an unreadable config means this script cannot assert the
    # thing it exists to assert, and warnings do not affect the exit status.
    *)     fail "cannot read the $MCP_SCOPE MCP config for $_name — nothing here is verified"
           note "$(printf '%s' "$info" | jget error)"
           return 1 ;;
  esac

  if [ "$(printf '%s' "$info" | jget entry_object)" != True ]; then
    fail "the $_name entry in $MCP_SCOPE scope is not a JSON object — it cannot start"
    note "re-run install.sh --only register"
    return 1
  fi

  # A registration naming the right flags on the wrong binary is not this
  # skill's server, however well-formed it looks.
  _cmd="$(printf '%s' "$info" | jget command)"
  if [ "$(basename "$_cmd")" != "$_bin" ]; then
    fail "$_name is registered to run '${_cmd:-(no command)}', not $_bin"
    note "re-run install.sh --only register"
    return 1
  fi

  _miss="$(printf '%s' "$info" | jget missing_args)"
  if [ -n "$_miss" ]; then
    fail "$_name registered without: $_miss"
    note "args: $(printf '%s' "$info" | jget args)"
    note "re-run install.sh --only register"
    return 1
  fi

  pass "$_name registered ($MCP_SCOPE scope): $_cmd"
  return 0
}

# --loogle-local is queried separately from the required set so a missing flag
# gets its own diagnosis rather than a generic "registered without".
LSP_Q="--require-arg=--repl --opt-value=--lean-project-path --env-key=LOOGLE_URL --has-arg=--loogle-local"
if check_registration lean-lsp lean-lsp-mcp $LSP_Q; then
  # A server pointed at a *different* Lean project answers every query happily
  # and about the wrong code, so the path is compared exactly, not merely present.
  p="$(printf '%s' "$info" | jget opt_value)"
  if [ "$(printf '%s' "$info" | jget opt_present)" != True ]; then
    fail "registered without --lean-project-path — the server will guess a project"
  elif [ "$p" = "$PROJ" ]; then
    pass "--lean-project-path is this project"
  else
    fail "--lean-project-path is '$p', not the project being verified"
    note "expected $PROJ"
  fi

  if ! skipped loogle; then
    case "$(printf '%s' "$info" | jget has_arg)" in
      True) pass "registered with --loogle-local" ;;
      *) fail "registered WITHOUT --loogle-local — lean_loogle is on the remote API"
         note "args: $(printf '%s' "$info" | jget args)"
         note "run install.sh --only register, or --skip loogle to accept remote deliberately" ;;
    esac

    # The exact endpoint, and a FAIL rather than a WARN: warnings do not affect
    # the exit status, so a fallback-capable registration would still exit 0.
    # Any reachable LOOGLE_URL — the public service most of all — leaves the
    # runtime fallback open, which is the whole point of pinning it.
    url="$(printf '%s' "$info" | jget env_value)"
    if [ "$(printf '%s' "$info" | jget env_present)" != True ]; then
      fail "LOOGLE_URL not set — an upstream runtime failure falls back to the remote API silently"
      note "re-run install.sh --only register to pin it"
    elif [ "$url" = "$LOOGLE_NULL_BACKEND" ]; then
      pass "LOOGLE_URL pinned to the dead endpoint; a runtime fallback cannot pass unnoticed"
    else
      fail "LOOGLE_URL is set to something reachable — the runtime fallback is still open"
      note "expected $LOOGLE_NULL_BACKEND; found $url"
    fi
  fi
fi

# `lean-explore mcp serve --backend local`. The backend is the whole point: the
# same binary registered without it, or with the hosted backend, needs
# LEANEXPLORE_API_KEY and answers from the network.
if check_registration lean-explore lean-explore \
     --require-arg=mcp --require-arg=serve --opt-value=--backend; then
  b="$(printf '%s' "$info" | jget opt_value)"
  if [ "$b" = local ]; then
    pass "--backend local; queries are served from the local index"
  else
    fail "registered with --backend '${b:-(unset)}', not local — this is the hosted API"
    note "args: $(printf '%s' "$info" | jget args)"
  fi
fi

if ! have claude; then
  note "claude CLI missing, but the config files were read directly"
fi

fi

summary "Verify"
