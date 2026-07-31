#!/usr/bin/env python3
"""A deterministic blank-line-framed stand-in for the Lean community REPL."""

from __future__ import annotations

import json
import re
import sys
import time
from pathlib import Path


environments: list[set[str]] = []


def new_environment(names: set[str]) -> int:
    environments.append(names)
    return len(environments) - 1


def answer(request: dict[str, object]) -> dict[str, object]:
    if "path" in request:
        text = Path(str(request["path"])).read_text(encoding="utf-8")
        names = set(re.findall(r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*)", text))
        return {"env": new_environment(names)}

    code = str(request.get("cmd", ""))
    if "CRASH_REPL" in code:
        print("deliberate fake REPL crash", file=sys.stderr, flush=True)
        raise SystemExit(23)
    if "SLEEP_REPL" in code:
        time.sleep(2)

    if "import Missing" in code:
        # The real REPL can silently return an empty environment when an import
        # command fails.  The following validation probe then fails with this
        # misleading symptom instead of identifying the missing module.
        return {
            "messages": [
                {"severity": "error", "data": "Unknown identifier `True`"}
            ],
            "env": new_environment(set()),
        }

    if "env" in request:
        base = set(environments[int(request["env"])])
    else:
        base = set()

    if "HUGE_REPL" in code:
        return {
            "messages": [{"severity": "info", "data": "x" * 4096}],
            "env": new_environment(base),
        }

    if "MANY_WARNINGS_ERROR" in code:
        messages = [
            {"severity": "warning", "data": f"warning {index}"}
            for index in range(101)
        ]
        messages.append({"severity": "error", "data": "late error"})
        return {"messages": messages, "env": new_environment(base)}

    if "TYPE_ERROR" in code:
        return {
            "messages": [
                {
                    "severity": "error",
                    "pos": {"line": 1, "column": 0},
                    "data": "synthetic type error",
                }
            ],
            "env": new_environment(base),
        }

    check = re.search(r"#check\s+([A-Za-z_][A-Za-z0-9_']*)", code)
    if check:
        name = check.group(1)
        severity = (
            "info" if name in base or name in {"Nat", "String", "True"} else "error"
        )
        data = f"{name} : Type" if severity == "info" else f"unknown identifier '{name}'"
        return {
            "messages": [
                {
                    "severity": severity,
                    "pos": {"line": 1, "column": 0},
                    "endPos": {"line": 1, "column": len(code)},
                    "data": data,
                }
            ],
            "env": new_environment(base),
        }

    for name in re.findall(r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*)", code):
        base.add(name)
    response: dict[str, object] = {"env": new_environment(base)}
    if "sorry" in code:
        response["sorries"] = [
            {
                "goal": "⊢ True",
                "proofState": 0,
                "pos": {"line": 1, "column": 0},
                "endPos": {"line": 1, "column": 5},
            }
        ]
    return response


def main() -> None:
    frame: list[str] = []
    for line in sys.stdin:
        if line.strip():
            frame.append(line)
            continue
        if not frame:
            continue
        request = json.loads("".join(frame))
        frame.clear()
        print(json.dumps(answer(request), indent=2), flush=True)
        print(flush=True)


if __name__ == "__main__":
    main()
