#!/usr/bin/env python3
"""exempt_export.py EXPORT OUT - nanoda's copy of a lean4export file, with the exempt theorems turned into axioms.

The independent check (docs/testing.md, "The independent check") has nanoda, a second kernel, re-check every declaration of a shard's export. A few declarations are beyond nanoda: it does not
finish them within any bound (its definitional-equality check unfolds without end and its memory grows until the runner is out of it), where the Lean kernel accepts them. Those are listed in
`scripts/ci/independent_check_exempt.json` (the workflow copies its own commit's list to `exempt-list.json`, where this reads it), by name, each with the library, the reason and where it was found. A change to that file is a change to what the check guarantees: it lies under scripts/ci/, so
it needs the approver's review like every other change to the check.

For the names in the list this writes OUT: the export with each such theorem's line replaced by an axiom of the same name, level parameters and type (nanoda then takes its statement for granted and checks
everything else against it). The axiom scan reads the original export, so the exempt theorem's own axioms are still audited; the Lean kernel has accepted it at build time. Only theorems can be exempt: a
definition replaced by an axiom would change what the declarations that unfold it mean. `exempt-applied.json` says which names this export held, and the sha256 of the list; the report job
refuses a check in which a listed name was applied nowhere, or one was applied that is not listed.

When no exempt name occurs in the export, OUT is not written (the caller checks the export as it is) and `exempt-applied.json` says so.

  exempt_export.py EXPORT OUT        EXPORT and OUT lie in the working directory or the temporary directory (RUNNER_TEMP)
"""

from __future__ import annotations

import hashlib
import json
import mmap
import sys
from array import array
from pathlib import Path
from typing import BinaryIO

from axiom_scan import checked_path

EXEMPT_FILE = Path("exempt-list.json")  # scripts/ci/independent_check_exempt.json at the workflow's commit: the workflow writes it here
APPLIED_JSON = Path("exempt-applied.json")
MIN_REASON = 40  # a reason that says what was seen and where, not a word


def load_exempt(text: str) -> dict[str, dict]:
    """name -> entry of the list; SystemExit when the list is not well formed (sorted by name, no duplicates, each entry with a name, the library it belongs to and a reason)"""
    doc = json.loads(text)
    entries = doc.get("exempt") if isinstance(doc, dict) else None
    if not isinstance(entries, list):
        raise SystemExit('the exempt list is {"exempt": [...]}')
    problems: list[str] = []
    out: dict[str, dict] = {}
    for e in entries:
        name = e.get("name") if isinstance(e, dict) else None
        if not isinstance(name, str) or not name:
            problems.append(f"an entry without a name: {e!r}")
            continue
        if name in out:
            problems.append(f"{name} is listed twice")
        for key in ("library", "reason"):
            if not isinstance(e.get(key), str) or not e[key].strip():
                problems.append(f"{name}: no {key}")
        if isinstance(e.get("reason"), str) and len(e["reason"].strip()) < MIN_REASON:
            problems.append(f"{name}: the reason has to say what was seen and where (at least {MIN_REASON} characters)")
        out[name] = e
    if list(out) != sorted(out):
        problems.append("the entries are not sorted by name")
    if problems:
        raise SystemExit("the exempt list is not well formed:\n  " + "\n  ".join(problems))
    return out


def occurs(export: Path, wanted: set[str]) -> bool:
    """whether the last component of any wanted name is a string of the export's name table: a scan of the file for the bytes, which decides whether the export needs rewriting at all"""
    needles = [b'"str":' + json.dumps(n.rsplit(".", 1)[-1]).encode("utf-8") for n in wanted]
    with open(export, "rb") as f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as m:
        return any(m.find(needle) != -1 for needle in needles)


def qualified(pre: array, part: list[str], i: int) -> str:
    parts: list[str] = []
    while i:
        parts.append(part[i])
        i = pre[i]
    return ".".join(reversed(parts))


def transform(src: BinaryIO, dst: BinaryIO, wanted: set[str]) -> list[str]:
    """copy the export line by line; a theorem named in `wanted` becomes an axiom with the same name, level parameters and type, a definition or opaque constant named in it is an error. The names applied, sorted."""
    pre = array("I", [0])
    part = [""]
    applied: list[str] = []
    for line in src:
        if b'"ie":' in line or b'"il":' in line:  # a term or a universe level: the bulk of the file, copied unread
            dst.write(line)
            continue
        o = json.loads(line)
        if "in" in o:
            v = o.get("str") or o["num"]
            pre.append(v["pre"])
            part.append(v["str"] if "str" in v else str(v["i"]))
            dst.write(line)
            continue
        kind = next((k for k in ("thm", "def", "opaque") if k in o), None)
        if kind is None:
            dst.write(line)
            continue
        v = o[kind]
        name = qualified(pre, part, v["name"])
        if name not in wanted:
            dst.write(line)
            continue
        if kind != "thm":
            raise SystemExit(
                f"{name} is listed as exempt but is a {'definition' if kind == 'def' else 'opaque constant'}: only theorems can be exempt"
            )
        axiom = {"axiom": {"name": v["name"], "levelParams": v["levelParams"], "type": v["type"], "isUnsafe": False}}
        dst.write(json.dumps(axiom, separators=(",", ":"), sort_keys=True).encode("utf-8") + b"\n")
        applied.append(name)
    return sorted(applied)


def write(path: Path, text: str) -> None:
    """`open` on the fixed path of this module and a write of the text (not Path.write_text: SonarCloud takes the text for a path)"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    export, out = checked_path(Path(argv[0])), checked_path(Path(argv[1]))
    text = EXEMPT_FILE.read_text(encoding="utf-8")
    wanted = set(load_exempt(text))
    sha = hashlib.sha256(text.encode("utf-8")).hexdigest()
    applied: list[str] = []
    if wanted and occurs(export, wanted):
        with open(export, "rb") as src, open(out, "wb") as dst:
            applied = transform(src, dst, wanted)
        if not applied:  # the bytes occurred, the theorems did not: nothing was changed, the copy is not needed
            out.unlink()
    write(APPLIED_JSON, json.dumps({"file_sha256": sha, "applied": applied}, indent=1) + "\n")
    print(
        f"exempt: {len(applied)} of the {len(wanted)} listed theorems are in this export"
        + (f" ({', '.join(applied)}), written as axioms to {out.name}" if applied else "")
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
