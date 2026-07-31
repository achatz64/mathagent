#!/usr/bin/env python3
"""Extract referenceable mathematical environments from the GT TeX source.

This is intentionally a small, dependency-free inventory tool rather than a
general LaTeX parser.  It records the source order, enclosing chapter/section,
labels, and bodies of the environments used by GT.tex.  Exercise and solution
material is excluded by default because it is outside the current experiment.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


ENVIRONMENTS = {
    "definition",
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "example",
    "remark",
    "question",
    "plain",
    "summary",
    "aside",
}

SKIP_CHAPTERS = {
    "Additional Exercises",
    "Solutions to the Exercises",
    "Two-Hour Examination",
}


def clean_tex(text: str) -> str:
    text = re.sub(r"%.*", "", text)
    return re.sub(r"\s+", " ", text).strip()


def heading(line: str, command: str) -> str | None:
    match = re.search(rf"\\{command}\{{(.*?)\}}", line)
    return clean_tex(match.group(1)) if match else None


def extract(path: Path) -> list[dict[str, object]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    chapter = "Front matter"
    section = ""
    subsection = ""
    records: list[dict[str, object]] = []
    index = 0

    while index < len(lines):
        line = lines[index]
        if value := heading(line, "chapter"):
            chapter, section, subsection = value, "", ""
        elif value := heading(line, "section"):
            section, subsection = value, ""
        elif value := heading(line, "subsection"):
            subsection = value

        begin = re.search(r"\\begin\{([^}]+)\}", line)
        if not begin or begin.group(1) not in ENVIRONMENTS:
            index += 1
            continue

        environment = begin.group(1)
        start = index
        body_lines = [line[begin.end() :]]
        end_marker = rf"\end{{{environment}}}"
        index += 1
        while index < len(lines) and end_marker not in lines[index]:
            body_lines.append(lines[index])
            index += 1
        if index < len(lines):
            body_lines.append(lines[index].split(end_marker, 1)[0])

        body = "\n".join(body_lines)
        labels = re.findall(r"\\label\{([^}]+)\}", body)
        skip = (
            chapter in SKIP_CHAPTERS
            or "Exercises" in section
            or environment == "exercise"
        )
        records.append(
            {
                "environment": environment,
                "line": start + 1,
                "end_line": index + 1,
                "chapter": chapter,
                "section": section,
                "subsection": subsection,
                "labels": labels,
                "included": not skip,
                "text": clean_tex(body),
            }
        )
        index += 1

    return records


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--all", action="store_true", help="include excluded material")
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--chapter", help="keep chapters containing this text")
    parser.add_argument(
        "--kinds",
        help="comma-separated environment names to keep",
    )
    args = parser.parse_args()
    records = extract(args.source)
    if not args.all:
        records = [record for record in records if record["included"]]
    if args.chapter:
        records = [
            record
            for record in records
            if args.chapter.casefold() in str(record["chapter"]).casefold()
        ]
    if args.kinds:
        kinds = set(args.kinds.split(","))
        records = [record for record in records if record["environment"] in kinds]
    if args.summary:
        counts: dict[str, int] = {}
        for record in records:
            environment = str(record["environment"])
            counts[environment] = counts.get(environment, 0) + 1
        print(json.dumps({"total": len(records), "counts": counts}, indent=2))
    else:
        print(json.dumps(records, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
