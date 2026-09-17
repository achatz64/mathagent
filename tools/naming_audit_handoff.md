# Handoff: `tools/naming_audit.py` is not trustable

Auditor finding, 2026-08-20 (delta audit of `lean/Target.lean`). Per the main
agent's decision, **fixing the tool is out of scope of the audit**; this file
records the evidence so a builder can repair or replace it.

## Verdict

Do not use the tool's output as audit evidence until the defects below are
fixed. Its central design claim ("self-validating: a flag == a genuine
snake_case deviation") does not hold at runtime.

## Defects (all reproduced on 2026-08-20)

### 1. The matcher does not consult its own allowlist cache
`--verify` and plain runs flag `Equiv`, `Module`, `Action`, `Basis`, `Linear`,
`MulEquiv` as `[high]` violations, although all six are present in
`tools/.mathlib_names.json` (23,125 entries, verified with a direct JSON
lookup). The allowlist is built but not effectively used during token
classification. Current output: **108 `[high]` findings** of unknown validity.

### 2. The status header documents mechanisms that do not exist in the code
The BUILDER STATUS REPORT (top of file) describes `SEED_ATOMS` and
`KNOWN_EXCEPTIONS` as load-bearing (e.g. `leftCoset` seeded; two documented
intentional exceptions registered there). Grep confirms **neither identifier is
defined in the script** — they exist only in comments. Consequences:
* `leftCoset`/`Coset` are flagged although the header promises they are seeded
  (neither token is in the cache either).
* The two documented intentional exceptions
  (`Group.sum_card_conjClasses_eq_card`, `IsPGroup.card_modEq_card_fixedPoints`,
  both marked "Coding-conventions AUDIT-GAP resolved" in `lean/Target.lean`)
  have no registration path and would be re-flagged as fresh violations.
* Also contradictory: the code comment block says "No hardcoded name lists",
  while the status header describes hardcoded seed lists.

### 3. The documented "resolved state" is stale
Header claims "the checker reports 0 high-confidence findings on the file";
actual output today is 108 findings. Contributors: defects 1–2, plus names
added after the tool/cache state it describes (the PID/Coxeter layers landed in
`e7cbcb9`, 2026-08-16, after the cache was built at 2026-08-16 00:13).

## Reproduction

```sh
python3 tools/naming_audit.py lean/Target.lean          # 108 [high] findings
python3 tools/naming_audit.py --verify lean/Target.lean # still flags Equiv, Module, ...
grep -n "SEED_ATOMS\|KNOWN_EXCEPTIONS" tools/naming_audit.py  # comments only
python3 - <<'EOF'
import json
names = set(json.load(open('tools/.mathlib_names.json')))
print([t for t in ['Equiv','Module','Action','Basis','Linear','MulEquiv'] if t in names])
# -> all six present, yet all six are flagged by the tool
EOF
```

## Impact on the 2026-08-20 delta audit — none

* The new contextual-naming rule was assessed **manually** (all 134
  constructions vs. their docstrings); 6 flags inserted in `lean/Target.lean`.
  This did not rely on the tool.
* The old rule (Mathlib name *form*) is outside the delta scope, and
  `lean/Target.lean`'s names are byte-identical to the passed
  `Extlib/GroupTheory/Mil21.lean` (the audit diff was documentation-only), so
  there is **no regression versus the passed state** regardless of the tool.

## Suggested builder tasks

1. Fix token classification to actually consult the allowlist cache (and the
   denyset) before flagging; investigate why cached atoms are still flagged.
2. Implement `SEED_ATOMS` and `KNOWN_EXCEPTIONS` or remove them from the docs;
   make the status header match the code.
3. Decide the intended treatment of `leftCoset`/`Coset`-style Mathlib atoms
   kept lowercase inside theorem names.
4. Add a self-test: assert that known-good Mathlib atoms (`Equiv`, `Module`,
   `MulEquiv`, `leftCoset`, ...) are never flagged.
5. Rebuild `tools/.mathlib_names.json` / `.mathlib_denyset.json` after the fix
   (`--rebuild-cache`), then re-run over the names added since 2026-08-16
   (PID/Coxeter layers) to recover a trustworthy form-conformance baseline.
