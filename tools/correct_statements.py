#!/usr/bin/env python3
"""correct_statements.py FILE... --by WHO --at DATE --reason TEXT [--write]

For a tentative records file, the `statement_correction` lines (schemas/record.schema.json) for the records whose statement and proof the extractor of today splits differently from the
way they were harvested (tengoku#811: a `:=` of a let/have in the type, or the arms of a match, ended the statement early). The text of a record is its statement and its proof joined by a
space, extracted again by tools/lean_extract.py: the same declaration comes back split where it should be. Used for tengoku#832 (498 lines over 7 libraries).

A line is made only when (a) the new split differs from the record's current text, (b) the validator would accept it (its own `moves_only`, read from scripts/ci/validate_records.py, and a statement
that only grows), and (c) the split does not depend on the character joining the statement and the proof: a proof that starts with a match arm `| ...` is only an arm at the start of a line, and joined
by a space it was pulled into the statement (135 of the 642 lines of the first version of tengoku#832: finite-simple-groups-lean, sandrones-library, tda-lib). Retracted names and records that cannot be extracted again are left alone. The file is not changed unless --write, which appends.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_extract  # noqa: E402


def _rules_from_validator():
    """validate_records.py runs on import (it reads argv), so its rules are taken from its source: the helper never drifts from what the gate accepts (moves_only, SEAM, AT_RE)."""
    import ast

    src = (Path(__file__).resolve().parent.parent / "scripts" / "ci" / "validate_records.py").read_text(encoding="utf-8")
    env: dict = {"re": re}
    for node in ast.parse(src).body:
        is_name = isinstance(node, ast.Assign) and any(getattr(t, "id", "") in ("SEAM", "AT_RE") for t in node.targets)
        if is_name or (isinstance(node, ast.FunctionDef) and node.name == "moves_only"):
            exec(compile(ast.Module([node], []), "validate_records.py", "exec"), env)
    return env["moves_only"], env["AT_RE"]


moves_only, AT_RE = _rules_from_validator()


def trusted_names(root: Path) -> set[str]:
    """The names of data/trusted, found as validate_records.trusted_names finds them: the gate refuses a correction of a trusted name (its text is the compiled one)."""
    out: set[str] = set()
    for f in (root / "data" / "trusted").rglob("*.jsonl"):
        with f.open("rb") as fh:
            for line in fh:
                m = re.search(rb'"name"\s*:\s*"([^"]+)"', line)
                if m:
                    out.add(m.group(1).decode())
    return out


def squash(s: str) -> str:
    return re.sub(r"\s+", "", s)


def _split(name: str, text: str) -> tuple[str, str] | None:
    for d in lean_extract.extract_declarations(text):
        if name == d.name or name.endswith("." + d.name):
            return d.statement, d.proof
    return None


def resplit(name: str, statement: str, proof: str) -> tuple[str, str] | None:
    """The statement and proof as today's extractor splits the record's text, or None when it cannot be extracted again, or when the answer depends on the character joining the two
    fields (a space or a newline): a proof that starts with a match arm `| ...` is only an arm at the start of a line, and joined by a space it would be pulled into the statement
    (tengoku#832, gitar: 135 lines of finite-simple-groups-lean, sandrones-library and tda-lib)."""
    by_newline = _split(name, statement.rstrip() + "\n" + proof.lstrip())
    by_space = _split(name, statement + " " + proof)
    if by_newline is None or by_space is None or tuple(map(squash, by_newline)) != tuple(map(squash, by_space)):
        return None
    return by_newline


def acceptable(old: tuple[str, str], new: tuple[str, str]) -> bool:
    """What validate_records.py accepts of a correction (its own `moves_only`, and a statement that only grows): nothing added or rewritten, the seam moved later."""
    (os_, op), (ns, np) = old, new
    if not ns.strip() or new == old:
        return False
    return moves_only(os_, op, ns, np) and ns.rstrip().startswith(os_.rstrip())


def corrections(text: str, by: str, at: str, reason: str, trusted: frozenset[str] | set[str] = frozenset()) -> list[dict]:
    """The correction lines for the records of one tentative file's text (the newest correction of a name is the record's current text)."""
    current: dict[str, tuple[str, str]] = {}
    retracted: set[str] = set()
    for line in text.splitlines():
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if not isinstance(r, dict):
            continue
        if isinstance(r.get("tombstone"), str):
            retracted.add(r["tombstone"])
        elif isinstance(r.get("statement_correction"), str):
            if isinstance(r.get("statement"), str) and isinstance(r.get("proof"), str):
                current[r["statement_correction"]] = (r["statement"], r["proof"])
        elif isinstance(r.get("name"), str) and isinstance(r.get("statement"), str) and isinstance(r.get("proof"), str):
            current[r["name"]] = (r["statement"], r["proof"])
    out = []
    for name, old in current.items():
        if name in retracted or name in trusted:
            continue
        new = resplit(name, *old)
        if new is not None and acceptable(old, new):
            out.append({"statement_correction": name, "statement": new[0], "proof": new[1], "reason": reason, "by": by, "at": at})
    return out


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("files", nargs="+")
    ap.add_argument("--by", required=True)
    ap.add_argument("--at", required=True)
    ap.add_argument("--reason", required=True)
    ap.add_argument("--write", action="store_true")
    a = ap.parse_args(argv)
    if not AT_RE.fullmatch(a.at) or not a.reason.strip() or "\n" in a.reason or len(a.reason) > 300:
        print("--at is a date (YYYY-MM-DD) and --reason one line of at most 300 characters, as the gate wants them", file=sys.stderr)
        return 2
    trusted = trusted_names(Path(__file__).resolve().parent.parent)
    total = 0
    for f in a.files:
        p = Path(f)
        text = p.read_text(encoding="utf-8")
        lines = [json.dumps(c, ensure_ascii=False) + "\n" for c in corrections(text, a.by, a.at, a.reason, trusted)]
        print(f"{f}: {len(lines)} statement corrections")
        total += len(lines)
        if a.write and lines:
            with p.open("a", encoding="utf-8") as fh:
                if text and not text.endswith("\n"):
                    fh.write("\n")
                fh.writelines(lines)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
