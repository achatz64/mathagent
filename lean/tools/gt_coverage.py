#!/usr/bin/env python3
"""Audit stable TeX labels mentioned by the canonical Lean target.

This deliberately checks comments rather than declaration names: the experiment
uses Mathlib-style names, while stable TeX labels are provenance annotations.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from gt_inventory import extract


THEOREM_LIKE = {"theorem", "lemma", "proposition", "corollary"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    args = parser.parse_args()

    records = [
        record
        for record in extract(args.source)
        if record["included"] and record["environment"] in THEOREM_LIKE
    ]
    source_labels = {
        label
        for record in records
        for label in record["labels"]
    }
    target_text = args.target.read_text(encoding="utf-8")
    mentioned = set(re.findall(r"`([A-Za-z][A-Za-z0-9]*)`", target_text))
    covered = sorted(source_labels & mentioned)
    missing = sorted(source_labels - mentioned)
    print(
        json.dumps(
            {
                "theorem_like_environments": len(records),
                "source_labels": len(source_labels),
                "labels_mentioned_in_target": len(covered),
                "unmentioned_labels": missing,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
