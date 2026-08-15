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

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
# This script lives in `tools/`; the certification package is the sibling `upstream/`.
ROOT = SCRIPT_DIR.parent / "upstream"
# Pristine mathlib source (already in the `upstream` package's dependency store).
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"


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
        assert e["oldText"] in src, f"anchor not found in {orig.name}: {e['oldText']!r}"
        src = src.replace(e["oldText"], e["newText"])
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
