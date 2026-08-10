#!/usr/bin/env python3
"""Audit stable TeX labels mentioned by the canonical Lean target.

This deliberately checks comments rather than declaration names: the experiment
uses Mathlib-style names, while stable TeX labels are provenance annotations.

The theorem-like report is retained for compatibility, but it is not a complete
source audit: GT also puts referenceable claims in definitions, examples,
remarks, plain prose, summaries, and asides.  The all-environment report makes
those labels visible instead of silently treating them as out of scope.
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

    included_records = [record for record in extract(args.source) if record["included"]]
    theorem_records = [
        record
        for record in included_records
        if record["environment"] in THEOREM_LIKE
    ]

    def labels(records: list[dict[str, object]]) -> set[str]:
        return {str(label) for record in records for label in record["labels"]}

    theorem_labels = labels(theorem_records)
    all_labels = labels(included_records)
    target_text = args.target.read_text(encoding="utf-8")
    mentioned = set(re.findall(r"`([A-Za-z][A-Za-z0-9]*)`", target_text))

    missing_by_environment: dict[str, list[str]] = {}
    for record in included_records:
        missing = sorted(set(map(str, record["labels"])) - mentioned)
        if missing:
            environment = str(record["environment"])
            missing_by_environment.setdefault(environment, []).extend(missing)
    missing_by_environment = {
        environment: sorted(set(environment_labels))
        for environment, environment_labels in sorted(missing_by_environment.items())
    }

    print(
        json.dumps(
            {
                "theorem_like_environments": len(theorem_records),
                "source_labels": len(theorem_labels),
                "labels_mentioned_in_target": len(theorem_labels & mentioned),
                "unmentioned_labels": sorted(theorem_labels - mentioned),
                "all_included_environments": len(included_records),
                "all_source_labels": len(all_labels),
                "all_labels_mentioned_in_target": len(all_labels & mentioned),
                "all_unmentioned_labels": sorted(all_labels - mentioned),
                "all_unmentioned_labels_by_environment": missing_by_environment,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
