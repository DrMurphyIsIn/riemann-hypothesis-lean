#!/usr/bin/env python3
"""Check that telperion/ differs from the development repository only where CENSORING.md says it does.

Usage:  python3 scripts/check_telperion_copy.py <path-to-an-Arda-checkout> [--show-diff]

The Arda checkout must be at the commit recorded in telperion/SYNC (scripts/materialize.sh makes one in
work/arda). Every file under telperion/ is compared with the file at the same path in Arda's telperion/:

  * byte-identical                                   -> fine;
  * a Python file whose syntax tree is the same once docstrings are removed (comments never reach the
    tree)                                            -> "comments/docstrings only";
  * a Python generator listed in CENSORING.md as an emitted-comment exception, whose syntax tree is the
    same once every string constant is blanked     -> "text of an emitted comment only";
  * a Lean file that is the same once comments are removed
                                                     -> "comments only";
  * anything else (prose, logs, data)                -> must be listed in CENSORING.md (--show-diff prints the diff;
                                                        it is off by default so the removed text stays out of logs);
  * a file with no counterpart in Arda               -> must be listed in CENSORING.md as added.

It exits non-zero if any code changed or any difference is unlisted.
"""
import ast
import difflib
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
COPY = HERE / "telperion"


def strip_docstrings(tree, blank_strings=False):
    for node in ast.walk(tree):
        if blank_strings and isinstance(node, ast.Constant) and isinstance(node.value, str):
            node.value = ""
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            body = node.body
            if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
                    and isinstance(body[0].value.value, str):
                node.body = body[1:] or [ast.Pass()]
    return ast.dump(tree, include_attributes=False)


def strip_lean_comments(text):
    out, i, depth, n = [], 0, 0, len(text)
    in_str = False
    while i < n:
        if depth == 0 and not in_str and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if not in_str and text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        c = text[i]
        if c == '"' and (i == 0 or text[i - 1] != "\\"):
            in_str = not in_str
        out.append(c)
        i += 1
    return re.sub(r"\s+", " ", "".join(out)).strip()


def main():
    args = [a for a in sys.argv[1:] if a != "--show-diff"]
    show = "--show-diff" in sys.argv[1:]
    if len(args) != 1:
        sys.exit(__doc__)
    arda = Path(args[0]).resolve() / "telperion"
    censoring = (HERE / "CENSORING.md").read_text()
    listed = set(re.findall(r"`(telperion/[^`]+)`", censoring))
    emitted = set(re.findall(r"`(telperion/[^`]+\.py)`[^\n]*emitted-comment exception", censoring))
    counts = {"identical": 0, "comments": 0, "listed": 0}
    bad = []
    tracked = subprocess.run(["git", "-C", str(HERE), "ls-files", "-z", "--cached", "--others", "--exclude-standard",
                              "telperion"], capture_output=True, check=True).stdout.decode().split("\0")
    for f in sorted(HERE / t for t in tracked if t):
        rel = f.relative_to(COPY)
        name = "telperion/" + rel.as_posix()
        src = arda / rel
        if not src.is_file():
            (counts.__setitem__("listed", counts["listed"] + 1) if name in listed
             else bad.append(f"ADDED, not listed in CENSORING.md: {name}"))
            continue
        a, b = src.read_bytes(), f.read_bytes()
        if a == b:
            counts["identical"] += 1
            continue
        if f.suffix == ".py":
            same = strip_docstrings(ast.parse(a)) == strip_docstrings(ast.parse(b))
            if not same and name in emitted:
                same = strip_docstrings(ast.parse(a), True) == strip_docstrings(ast.parse(b), True)
        elif f.suffix == ".lean":
            same = strip_lean_comments(a.decode()) == strip_lean_comments(b.decode())
        else:
            same = None
        if same is False:
            bad.append(f"CODE CHANGED: {name}")
            continue
        if name not in listed:
            bad.append(f"DIFFERS, not listed in CENSORING.md: {name}")
            continue
        counts["comments" if same else "listed"] += 1
        if same is None and not show:
            print(f"prose reworded (listed): {name}")
        elif same is None:
            print(f"--- prose diff: {name}")
            sys.stdout.writelines(difflib.unified_diff(a.decode().splitlines(True), b.decode().splitlines(True),
                                                       f"arda/{name}", name, n=0))
    print(f"\nidentical: {counts['identical']}; code identical, comments/docstrings reworded: {counts['comments']}; "
          f"prose reworded or added (listed in CENSORING.md): {counts['listed']}")
    for line in bad:
        print(line)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
