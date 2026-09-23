#!/usr/bin/env python3
"""attribute.py <dir> --credit "Author: …" — put your credit on every declaration.

A project with three hundred theorems should not need three hundred hand-written
docstrings before it is submitted. This walks the `.lean` files under a directory
and gives every theorem, lemma, definition, instance, structure, inductive and
class the credit as the last line of its docstring, writing the docstring where
there is none. Running it twice changes nothing; another author's credit is never
overwritten; commented-out code is never touched. README.md next to this file
has the rest.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

KINDS = ["theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive", "class", "opaque"]
_MODS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s+)*"
_KIND = r"(?P<kind>" + "|".join(KINDS) + r")\b"
# The line a declaration starts on: attributes and modifiers on that line, then the keyword.
DECL_RE = re.compile(r"^(?P<indent>[ \t]*)(?:@\[[^\]]*\]\s*)*" + _MODS + _KIND + r"(?:\s+(?P<name>[^\s(:{\[⦃]+))?")
# `/-- one line -/ theorem …`: the docstring and the declaration share a line.
INLINE_DOC_RE = re.compile(r"^(?P<indent>[ \t]*)/--(?P<doc>.*?)-/[ \t]*(?:@\[[^\]]*\]\s*)*" + _MODS + _KIND)
ATTR_BLOCK_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)+$")
MOD_LINE_RE = re.compile(r"^\s*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s*)+$")
# The marker the tree's checks key on (scripts/ci/credits.py, tools/lean_extract.py).
CREDIT_RE = re.compile(r"\bAuthors?:", re.I)


def lead_in_start(lines: list[str], i: int) -> int:
    """First line of the declaration's own lead-in: attribute lines (one attribute may
    span several) and modifier-only lines directly above line i. `open … in` and
    `set_option … in` are not part of it: a docstring goes below those."""
    h = i
    while h > 0:
        found = None
        for k in range(h - 1, max(-1, h - 12), -1):
            line = lines[k]
            if not line.strip():
                break
            if MOD_LINE_RE.match(line) or ATTR_BLOCK_RE.match("\n".join(lines[k:h])):
                found = k
                break
            if line.lstrip().startswith("@["):
                break
        if found is None:
            return h
        h = found
    return h


def docstring_above(lines: list[str], h: int) -> tuple[int, int] | None:
    """Bounds (first line, last line) of the `/-- … -/` directly above line h, blank
    lines allowed between; None for no docstring (a `/- … -/` or `/-! … -/` is not one)."""
    d = h - 1
    while d >= 0 and not lines[d].strip():
        d -= 1
    if d < 0 or not lines[d].rstrip().endswith("-/"):
        return None
    k, depth = d, 0
    while k >= 0:
        depth += lines[k].count("-/") - lines[k].count("/-")
        if depth <= 0:
            break
        k -= 1
    if k < 0 or not lines[k].lstrip().startswith("/--"):
        return None
    return k, d


def attribute_file(path: Path, credit: str, kinds: set[str], dry_run: bool) -> dict:
    text = path.read_text(encoding="utf-8")
    lines = text.split("\n")
    edits: list[tuple[str, int, object]] = []
    stats: dict = {"credited": 0, "already": 0, "other": []}

    def credit_docstring(indent: str, k: int, d: int, label: str, i: int) -> None:
        body = "\n".join(lines[k : d + 1])
        if credit in body:
            stats["already"] += 1
        elif CREDIT_RE.search(body):
            stats["other"].append(f"{path}:{i + 1} {label}")
        elif lines[d].strip() == "-/":
            edits.append(("insert", d, ([""] if lines[d - 1].strip() else []) + [f"{indent}{credit}"]))
            stats["credited"] += 1
        else:
            edits.append(("replace", d, re.sub(r"\s*-/", f"\n\n{indent}{credit} -/", lines[d], count=1)))
            stats["credited"] += 1

    depth = 0
    for i, line in enumerate(lines):
        if depth == 0:
            m = DECL_RE.match(line)
            inline = None if m else INLINE_DOC_RE.match(line)
            if m and m.group("kind") in kinds:
                indent, label = m.group("indent"), m.group("name") or m.group("kind")
                h = lead_in_start(lines, i)
                doc = docstring_above(lines, h)
                if doc is None:
                    edits.append(("insert", h, [f"{indent}/-- {credit} -/"]))
                    stats["credited"] += 1
                else:
                    credit_docstring(indent, doc[0], doc[1], label, i)
            elif inline and inline.group("kind") in kinds:
                credit_docstring(inline.group("indent"), i, i, inline.group("kind"), i)
        depth = max(0, depth + line.count("/-") - line.count("-/"))

    for op, idx, payload in sorted(edits, key=lambda e: -e[1]):
        if op == "insert":
            lines[idx:idx] = payload  # type: ignore[arg-type]
        else:
            lines[idx] = payload  # type: ignore[assignment]
    if edits and not dry_run:
        path.write_text("\n".join(lines), encoding="utf-8")
    return stats


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Write your credit into every declaration's docstring under a directory.")
    ap.add_argument("directory", type=Path, help="the Lean project (every .lean file under it, .lake/ skipped)")
    ap.add_argument(
        "--credit",
        required=True,
        help='one line starting with "Author:", e.g. "Author: Ada Lovelace (https://github.com/ada), with Claude"',
    )
    ap.add_argument(
        "--kinds", default=",".join(KINDS), help=f"declaration kinds to credit, comma-separated (default: all of {', '.join(KINDS)})"
    )
    ap.add_argument("--dry-run", action="store_true", help="report what would change; write nothing")
    a = ap.parse_args(argv)
    credit = " ".join(a.credit.split())
    if not CREDIT_RE.search(credit):
        ap.error("--credit must contain `Author:` (or `Authors:`): that is the marker the tree's checks key on")
    kinds = {k.strip() for k in a.kinds.split(",") if k.strip()}
    if kinds - set(KINDS):
        ap.error(f"unknown kinds: {', '.join(sorted(kinds - set(KINDS)))}")
    files = sorted(p for p in a.directory.rglob("*.lean") if ".lake" not in p.parts)
    if not files:
        print(f"no .lean files under {a.directory}", file=sys.stderr)
        return 1
    credited = already = 0
    other: list[str] = []
    for f in files:
        st = attribute_file(f, credit, kinds, a.dry_run)
        if st["credited"]:
            print(f"{f}: {st['credited']} {'would be ' if a.dry_run else ''}credited")
        credited += st["credited"]
        already += st["already"]
        other += st["other"]
    print(
        f"{'would credit' if a.dry_run else 'credited'} {credited} declarations in {len(files)} files; {already} already carried this credit"
    )
    if other:
        print(f"{len(other)} left alone, their docstring names another author:")
        for o in other:
            print(f"  {o}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
