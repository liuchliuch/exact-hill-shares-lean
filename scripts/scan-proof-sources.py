#!/usr/bin/env python3
"""Fail-closed lexical audit of the actual local proof-source inventory.

The environment audit separately checks every safe declaration's transitive
axioms. This source pass prevents explicit custom unsafe declarations/axioms from
hiding among excluded compiler IR. Nested comments and strings are skipped, so
documentation of the audit policy is not mistaken for a declaration.

This project intentionally has no custom declaration-generating metaprograms.
Those entry points are rejected as well; allowing them would require a separate
review of generated unsafe declarations rather than a lexical claim.
"""
from __future__ import annotations
import pathlib
import re
import sys

FORBIDDEN = {
    "axiom", "unsafe", "partial", "sorry", "admit",
    "run_cmd", "elab", "elab_rules", "macro", "macro_rules",
    "initialize", "builtin_initialize",
    "extern", "implemented_by", "native_decide",
}


def code_only(source: str) -> str:
    """Blank comments/string contents, retaining offsets and line numbers."""
    out = list(source)
    i, n = 0, len(source)
    def blank(start: int, stop: int) -> None:
        for j in range(start, stop):
            if out[j] != "\n":
                out[j] = " "
    while i < n:
        if source.startswith("--", i):
            end = source.find("\n", i)
            end = n if end == -1 else end
            blank(i, end); i = end
        elif source.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < n and depth:
                if source.startswith("/-", i): depth += 1; i += 2
                elif source.startswith("-/", i): depth -= 1; i += 2
                else: i += 1
            if depth: raise ValueError("Unterminated block comment")
            blank(start, i)
        elif source[i] == '"':
            start = i
            i += 1
            while i < n:
                if source[i] == "\\": i += 2
                elif source[i] == '"': i += 1; break
                else: i += 1
            else: raise ValueError("Unterminated string")
            blank(start, min(i, n))
        else:
            i += 1
    return "".join(out)


def inspect(path: pathlib.Path) -> list[str]:
    source = path.read_text()
    code = code_only(source)
    errors = []
    for match in re.finditer(r"(?<![\w'])[_A-Za-z][_A-Za-z0-9']*", code):
        if match.group() in FORBIDDEN:
            line = source.count("\n", 0, match.start()) + 1
            column = match.start() - source.rfind("\n", 0, match.start())
            errors.append(f"SOURCE_POLICY_REJECT\t{path}:{line}:{column}\t{match.group()}")
    return errors


def main() -> int:
    args = sys.argv[1:]
    if len(args) >= 2 and args[0] == "--manifest":
        paths = [pathlib.Path(line.split("\t", 1)[1])
                 for line in pathlib.Path(args[1]).read_text().splitlines() if line]
    else:
        paths = [pathlib.Path(arg) for arg in args]
    if not paths:
        print("No proof sources supplied; refusing a vacuous pass", file=sys.stderr)
        return 2
    errors = []
    for path in paths:
        try:
            errors.extend(inspect(path))
        except (OSError, ValueError) as exc:
            errors.append(f"SOURCE_SCAN_ERROR\t{path}\t{exc}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"SOURCE_POLICY_PASSED\t{len(paths)} files; no explicit axioms, unsafe declarations, admissions, or custom declaration generators")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
