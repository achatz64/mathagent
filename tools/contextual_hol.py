#!/usr/bin/env python3
"""Prototype contextual-HOL-to-Core translator.

Input is a small typed JSON AST.  The tool emits the canonical Core `Pred`
expression for the formula in the supplied object context.

This is intentionally modest: it is a convention checker/prototype, not a proof
checker and not a parser for human HOL notation.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class Binding:
    name: str
    type: str


@dataclass
class Env:
    constants: dict[str, str]
    relations: dict[str, tuple[str, str]]


def paren(s: str) -> str:
    return f"({s})"


SIMPLE_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'-]*$")


def type_arg(s: str) -> str:
    if SIMPLE_NAME.match(s):
        return s
    if s.startswith("(") and s.endswith(")"):
        return s
    return paren(s)


def ctx_type(ctx: list[Binding]) -> str:
    if not ctx:
        return "Final"
    head = ctx[0].type
    tail = ctx_type(ctx[1:])
    if tail == "Final":
        return f"{head} × Final"
    return f"{head} × ({tail})"


def context_from_json(raw: list[dict[str, str]]) -> list[Binding]:
    return [Binding(item["name"], item["type"]) for item in raw]


def env_from_json(raw: dict[str, Any]) -> Env:
    constants = dict(raw.get("constants", {}))
    relations_raw = raw.get("relations", {})
    relations: dict[str, tuple[str, str]] = {}
    for name, signature in relations_raw.items():
        if len(signature) != 2:
            raise ValueError(f"relation {name!r} must have exactly two argument types")
        relations[name] = (signature[0], signature[1])
    return Env(constants=constants, relations=relations)


def lookup_var(name: str, ctx: list[Binding]) -> int:
    for idx, binding in enumerate(ctx):
        if binding.name == name:
            return idx
    raise ValueError(f"unknown object variable {name!r}")


def named_projection(idx: int, ctx: list[Binding]) -> str | None:
    if idx > 3:
        return None
    tail = ctx_type(ctx[idx + 1 :])
    if idx == 0:
        return f"v0 {type_arg(ctx[0].type)} {type_arg(tail)}"
    if idx == 1:
        return f"v1 {type_arg(ctx[0].type)} {type_arg(ctx[1].type)} {type_arg(tail)}"
    if idx == 2:
        return (
            f"v2 {type_arg(ctx[0].type)} {type_arg(ctx[1].type)} "
            f"{type_arg(ctx[2].type)} {type_arg(tail)}"
        )
    return (
        f"v3 {type_arg(ctx[0].type)} {type_arg(ctx[1].type)} "
        f"{type_arg(ctx[2].type)} {type_arg(ctx[3].type)} {type_arg(tail)}"
    )


def raw_projection(idx: int, ctx: list[Binding]) -> str:
    """Projection for arbitrary depth using only fst/snd composition."""
    target = ctx[idx]
    first = f"fst {type_arg(target.type)} {type_arg(ctx_type(ctx[idx + 1 :]))}"
    parts = [paren(first)]
    for j in range(idx - 1, -1, -1):
        parts.append(paren(f"snd {type_arg(ctx[j].type)} {type_arg(ctx_type(ctx[j + 1 :]))}"))
    return " ∘ ".join(parts)


def projection(idx: int, ctx: list[Binding], use_named_projectors: bool) -> str:
    if use_named_projectors:
        named = named_projection(idx, ctx)
        if named is not None:
            return named
    return raw_projection(idx, ctx)


def term_type(term: dict[str, Any], env: Env, ctx: list[Binding]) -> str:
    if "var" in term:
        return ctx[lookup_var(term["var"], ctx)].type
    if "const" in term:
        name = term["const"]
        if name not in env.constants:
            raise ValueError(f"unknown constant/schema parameter {name!r}")
        return env.constants[name]
    if "core" in term:
        if "type" not in term:
            raise ValueError("raw core term must include a type")
        return term["type"]
    raise ValueError(f"unknown term node: {term!r}")


def translate_term(
    term: dict[str, Any],
    env: Env,
    ctx: list[Binding],
    use_named_projectors: bool,
) -> str:
    cty = ctx_type(ctx)
    if "var" in term:
        return projection(lookup_var(term["var"], ctx), ctx, use_named_projectors)
    if "const" in term:
        name = term["const"]
        ty = term_type(term, env, ctx)
        return f"Cart.weakening {type_arg(ty)} {type_arg(cty)} {name}"
    if "core" in term:
        return term["core"]
    raise ValueError(f"unknown term node: {term!r}")


def translate_formula(
    formula: dict[str, Any],
    env: Env,
    ctx: list[Binding],
    use_named_projectors: bool,
) -> str:
    cty = ctx_type(ctx)

    if "atom" in formula:
        atom = formula["atom"]
        rel = atom["rel"]
        if rel not in env.relations:
            raise ValueError(f"unknown relation {rel!r}")
        left_ty, right_ty = env.relations[rel]
        args = atom["args"]
        if len(args) != 2:
            raise ValueError(f"relation atom {rel!r} must have exactly two args")
        actual_left = term_type(args[0], env, ctx)
        actual_right = term_type(args[1], env, ctx)
        if actual_left != left_ty or actual_right != right_ty:
            raise ValueError(
                f"relation {rel!r} expects ({left_ty}, {right_ty}), "
                f"got ({actual_left}, {actual_right})"
            )
        left = translate_term(args[0], env, ctx, use_named_projectors)
        right = translate_term(args[1], env, ctx, use_named_projectors)
        return (
            f"sub2 {type_arg(cty)} {type_arg(left_ty)} {type_arg(right_ty)} "
            f"{rel} {paren(left)} {paren(right)}"
        )

    if "and" in formula:
        a, b = formula["and"]
        return (
            f"Pred.and {type_arg(cty)} "
            f"{paren(translate_formula(a, env, ctx, use_named_projectors))} "
            f"{paren(translate_formula(b, env, ctx, use_named_projectors))}"
        )

    if "or" in formula:
        a, b = formula["or"]
        return (
            f"Pred.or {type_arg(cty)} "
            f"{paren(translate_formula(a, env, ctx, use_named_projectors))} "
            f"{paren(translate_formula(b, env, ctx, use_named_projectors))}"
        )

    if "imply" in formula:
        a, b = formula["imply"]
        return (
            f"Pred.imply {type_arg(cty)} "
            f"{paren(translate_formula(a, env, ctx, use_named_projectors))} "
            f"{paren(translate_formula(b, env, ctx, use_named_projectors))}"
        )

    if "not" in formula:
        return (
            f"Pred.not {type_arg(cty)} "
            f"{paren(translate_formula(formula['not'], env, ctx, use_named_projectors))}"
        )

    if "forall" in formula:
        binder = formula["forall"]
        var = Binding(binder["var"], binder["type"])
        body_ctx = [var] + ctx
        body = translate_formula(binder["body"], env, body_ctx, use_named_projectors)
        return f"Forall {type_arg(var.type)} {type_arg(cty)} {paren(body)}"

    if "exists" in formula:
        binder = formula["exists"]
        var = Binding(binder["var"], binder["type"])
        body_ctx = [var] + ctx
        body = translate_formula(binder["body"], env, body_ctx, use_named_projectors)
        return f"Exist {type_arg(var.type)} {type_arg(cty)} {paren(body)}"

    raise ValueError(f"unknown formula node: {formula!r}")


def translate_document(doc: dict[str, Any], use_named_projectors: bool) -> str:
    env = env_from_json(doc.get("schema", {}))
    ctx = context_from_json(doc.get("context", []))
    pred = translate_formula(doc["formula"], env, ctx, use_named_projectors)
    if doc.get("as_pc", False):
        if ctx:
            raise ValueError("as_pc requires an empty top-level object context")
        return f"Pred.term {paren(pred)}"
    return pred


def demo_documents() -> list[tuple[str, dict[str, Any]]]:
    return [
        (
            "atom R(x,a) in context x:X",
            {
                "schema": {"constants": {"a": "X"}, "relations": {"R": ["X", "X"]}},
                "context": [{"name": "x", "type": "X"}],
                "formula": {
                    "atom": {"rel": "R", "args": [{"var": "x"}, {"const": "a"}]}
                },
            },
        ),
        (
            "closed forall x. R(x,a)",
            {
                "schema": {"constants": {"a": "X"}, "relations": {"R": ["X", "X"]}},
                "context": [],
                "as_pc": True,
                "formula": {
                    "forall": {
                        "var": "x",
                        "type": "X",
                        "body": {
                            "atom": {
                                "rel": "R",
                                "args": [{"var": "x"}, {"const": "a"}],
                            }
                        },
                    }
                },
            },
        ),
        (
            "exists w. R(w,A) and R(z,w)",
            {
                "schema": {
                    "constants": {"A": "X", "z": "X"},
                    "relations": {"R": ["X", "X"]},
                },
                "context": [],
                "as_pc": True,
                "formula": {
                    "exists": {
                        "var": "w",
                        "type": "X",
                        "body": {
                            "and": [
                                {
                                    "atom": {
                                        "rel": "R",
                                        "args": [{"var": "w"}, {"const": "A"}],
                                    }
                                },
                                {
                                    "atom": {
                                        "rel": "R",
                                        "args": [{"const": "z"}, {"var": "w"}],
                                    }
                                },
                            ]
                        },
                    }
                },
            },
        ),
    ]


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_file", nargs="?", help="JSON AST file; stdin if omitted")
    parser.add_argument("--demo", action="store_true", help="print built-in examples")
    parser.add_argument(
        "--raw-projectors",
        action="store_true",
        help="emit fst/snd compositions instead of v0..v3 when possible",
    )
    args = parser.parse_args(argv)

    use_named_projectors = not args.raw_projectors

    if args.demo:
        for label, doc in demo_documents():
            print(f"-- {label}")
            print(translate_document(doc, use_named_projectors))
            print()
        return 0

    if args.json_file:
        with open(args.json_file, encoding="utf-8") as handle:
            doc = json.load(handle)
    else:
        doc = json.load(sys.stdin)
    print(translate_document(doc, use_named_projectors))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
