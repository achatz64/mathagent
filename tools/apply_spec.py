#!/usr/bin/env python3
"""Generic insertion-spec applier for the upstream certification package.

For every candidate folder under this `upstream/` dir that contains `insertion_spec.json`,
read its `*.original.lean` (pristine copy of the mathlib `target_file`), neutralize
mathlib-only commands, apply the spec's edits, and write the generated shadow `<X>.lean`.
This mirrors exactly what the fork does when it applies the same spec to the real mathlib
file — so the shadow is a local, buildable stand-in for "target_file + our change".

Names are derived, never hardcoded:
  <candidate>/<base>.original.lean  -> pristine copy of spec["target_file"]
  <candidate>/<base>.lean           -> generated shadow (written here)
  <candidate>/insertion_spec.json   -> the insertion diff (pi `edit` format)

Usage: python3 apply_spec.py [relative_candidate_dir ...]   # default: all candidate folders
"""
import json
import pathlib
import re
import sys
from typing import List

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
# This script lives in `tools/`; the certification package is the sibling `upstream/`.
ROOT = SCRIPT_DIR.parent / "upstream"
# Pristine mathlib source (already in the `upstream` package's dependency store).
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"


def apply_edits(src: str, edits: List[dict], orig_name: str) -> str:
    """Apply spec edits mirroring the pi `edit` tool's semantics.

    All anchors are located in the *original* `src` (not in the progressively
    mutated buffer), each anchor must be unique, edits must not overlap, and the
    replacements are spliced positionally. This avoids the two bugs of a naive
    sequential `src.replace`: a repeated anchor being replaced everywhere, and a
    later edit matching text that an earlier edit just inserted or destroyed.
    """
    spans = []
    for i, e in enumerate(edits):
        old = e["oldText"]
        count = src.count(old)
        if count == 0:
            raise AssertionError(
                f"edit #{i}: anchor not found in {orig_name}: {old!r}")
        if count > 1:
            raise AssertionError(
                f"edit #{i}: anchor is not unique ({count} occurrences) in "
                f"{orig_name}: {old!r}")
        start = src.index(old)
        spans.append((start, start + len(old), e["newText"], i))
    # Reject overlapping (or nested) edits, exactly as pi does.
    spans.sort()
    for (s1, e1, _, i1), (s2, e2, _, i2) in zip(spans, spans[1:]):
        if s2 < e1:
            raise AssertionError(
                f"edits #{i1} and #{i2} overlap: "
                f"{edits[i1]['oldText']!r} / {edits[i2]['oldText']!r}")
    # Splice right-to-left so earlier indices stay valid.
    result = src
    for s, e, new, _ in sorted(spans, reverse=True):
        result = result[:s] + new + result[e:]
    return result


def process(cand: pathlib.Path) -> None:
    spec_path = cand / "insertion_spec.json"
    if not spec_path.exists():
        return
    spec = json.loads(spec_path.read_text())
    target = spec["target_file"]
    # Auto-fetch the pristine mathlib file (no hand-written copy needed).
    base = pathlib.Path(target).stem  # e.g. "Basic" for ".../Quotient/Basic.lean"
    orig = cand / f"{base}.original.lean"
    if not orig.exists():
        src_path = MATHLIB / target
        assert src_path.exists(), f"mathlib source not found: {src_path}"
        orig.write_text(src_path.read_text())
        print(f"fetched {orig.relative_to(ROOT)} from mathlib ({target})")
    src = orig.read_text()
    # Neutralize mathlib-only commands so the file compiles standalone in `Upstream`.
    # (The fork keeps them; it applies the spec to its own mathlib file.)
    src = src.replace("public import", "import").replace("public section", "section")
    src = re.sub(r"^module\s*$", "", src, flags=re.M)
    for e in spec["edits"]:
        assert e["path"] == target, f"edit path {e['path']!r} != target_file {target!r}"
    src = apply_edits(src, spec["edits"], orig.name)
    out = cand / orig.name.replace(".original.lean", ".lean")
    out.write_text(src)
    print(f"generated {out.relative_to(ROOT)} ({len(src.splitlines())} lines)")


def main() -> None:
    args = [pathlib.Path(a) for a in sys.argv[1:]]
    if args:
        for a in args:
            process(ROOT / a)
    else:
        # Process every candidate folder (any depth) that holds an insertion_spec.json.
        for spec_path in sorted(ROOT.rglob("insertion_spec.json")):
            if ".lake" in spec_path.parts:
                continue
            process(spec_path.parent)


if __name__ == "__main__":
    main()
