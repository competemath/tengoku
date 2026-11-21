#!/usr/bin/env python3
"""v2.py - Tengoku's dataset, version 2, and the migration from version 1 (docs/v2.md). Standard library only.

  v2.py migrate INPUT [--out OUT] [--ids IDS.tsv] [--map MAP.jsonl] [--library L]
      the one entry point. INPUT decides what happens:
        a snapshot directory (snapshot.json + tengoku-dataset.jsonl.gz) or a dataset file (.jsonl, .jsonl.gz)   -> the version 2 dataset (a version 2 input is returned unchanged)
        a Lean file or a directory of them (with --map)                                                          -> the source with renamed names rewritten, and a report of what is left
        any other text                                                                                          -> that name, reference or statement id resolved against --out's dataset
  v2.py check DATASET                    the invariants of a version 2 dataset (every violation is printed; exit 1)
  v2.py diff OLD NEW [--out MAP.jsonl]   what a version change did to every record: unchanged, corrected, moved, renamed, restated, removed, added

Version 1 (the 1.0.0 release) has no key: 14,911 of its 198,172 records share a (library, name) with another record; its `name` is wrong for 6,998 records (cut at the first non-ASCII character: `A` for
`A₂_mem_circumsphere`); and three of its twelve fields are null in every row. Version 2 gives every record a `ref`, repairs the cut names (`legacy_name` keeps what version 1 said), drops what is null,
renames the one clumsy field, and carries the statement identity (isnad, docs/isnad.md) when it is known. Everything version 1 said, version 2 says:
`downgrade(upgrade(r)) == r` for every version 1 record, and `upgrade` is a pure function of the version 1 data (plus the optional ids), so nobody needs a lookup table to migrate.
"""

from __future__ import annotations

import argparse
import difflib
import gzip
import hashlib
import json
import os
import re
import sys
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

SCHEMA = 2
# the version 1 fields, in the order snapshot.py writes them
V1_FIELDS = (
    "name",
    "library",
    "statement",
    "proof",
    "source_url",
    "licence",
    "credit",
    "toolchain",
    "promoted_at",
    "credit_corrected_evidence",
    "headline",
    "upstream",
)
# the version 2 fields: the required ones first, then the optional ones, which are left out when they do not apply
V2_REQUIRED = ("schema", "ref", "status", "name", "library", "statement", "proof", "source_url", "toolchain")
V2_OPTIONAL = ("id", "legacy_name", "module", "licence", "credit", "credit_evidence", "promoted_at", "headline", "upstream")
V2_FIELDS = V2_REQUIRED + V2_OPTIONAL
RENAMED_FIELD = ("credit_corrected_evidence", "credit_evidence")
ISNAD_ID = re.compile(r"^[a-z0-9]{1,8}\.\d+h\d+v\.s\d+\.[0-9a-f]{12}$")
REF = re.compile(r"^[^:\s]+:\S.*$")
BLOB = re.compile(r"/blob/[0-9a-f]{7,40}/(.+?)(?:#L\d+(?:-L\d+)?)?$")
CHANGES = ("unchanged", "corrected", "moved", "renamed", "restated", "removed", "added")


# ---------------------------------------------------------------------------------------------------------------- reading


def read_jsonl(path: Path) -> List[Dict[str, Any]]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as fh:  # type: ignore[operator]
        return [json.loads(line) for line in fh if line.strip()]


def write_jsonl(path: Path, rows: Iterable[Dict[str, Any]]) -> None:
    text = "".join(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n" for r in rows)
    if path.suffix == ".gz":
        path.write_bytes(gzip.compress(text.encode("utf-8"), mtime=0))  # mtime 0: the same rows make the same bytes
    else:
        path.write_text(text, encoding="utf-8")


def schema_of(rows: List[Dict[str, Any]]) -> int:
    """1 or 2; a dataset is one or the other, never both"""
    kinds = {r.get("schema", 1) for r in rows}
    if len(kinds) > 1:
        raise ValueError(f"mixed schemas {sorted(kinds)} in one dataset")
    return kinds.pop() if kinds else 1


# ---------------------------------------------------------------------------------------------------------------- identity


def module_of(source_url: Optional[str]) -> Optional[str]:
    """the Lean module a record's source file is, when source_url points into a .lean file of a repository"""
    m = BLOB.search(source_url or "")
    if not m or not m.group(1).endswith(".lean"):
        return None
    return m.group(1)[: -len(".lean")].replace("/", ".")


DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "structure",
    "inductive",
    "class",
    "axiom",
    "opaque",
    "irreducible_def",
    "example",
)
DECL_MODIFIERS = ("protected", "private", "noncomputable", "nonrec", "partial", "unsafe", "scoped", "local", "public", "meta")
DECL_NAME = re.compile(r"«[^»\n]*»|[^\s:({\[⟨,=]+")


def _skip_trivia(s: str, i: int) -> int:
    """past white space and comments (-- and nested /- -/)"""
    n = len(s)
    while i < n:
        if s[i].isspace():
            i += 1
        elif s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
        elif s.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if s.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif s.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            break
    return i


def _skip_attributes(s: str, i: int) -> int:
    """past a run of `@[...]` (brackets balanced, so `@[simp, to_additive foo]` and a nested `[` are fine)"""
    while s.startswith("@[", i):
        depth = 0
        while i < len(s):
            if s[i] == "[":
                depth += 1
            elif s[i] == "]":
                depth -= 1
                if depth == 0:
                    i += 1
                    break
            i += 1
        i = _skip_trivia(s, i)
    return i


def declared_name(statement: str) -> Optional[str]:
    """the name a statement declares, as written in its header: the first declaration after the imports, `open`s and attributes; None when there is none to read"""
    s, i = str(statement), 0
    for _ in range(60):
        i = _skip_attributes(s, _skip_trivia(s, i))
        word = re.match(r"[A-Za-z_@]+", s[i:])
        if not word:
            return None
        w = word.group(0)
        if w in DECL_MODIFIERS:
            i += len(w)
            continue
        if w in DECL_KEYWORDS:
            i = _skip_trivia(s, i + len(w))
            m = DECL_NAME.match(s[i:])
            return m.group(0) if m else None
        j = s.find("\n", i)  # an import, open, namespace, set_option ...: the rest of its line
        if j < 0:
            return None
        i = j
    return None


def repaired_name(record: Dict[str, Any]) -> str:
    """the name version 1 meant: it cut names at their first non-ASCII character (`A` for `A₂_mem_circumsphere`, 6,998 of the 198,172 records of 1.0.0), the header of the statement has the whole name.
    Only a cut is repaired: a name that is not a prefix of the header's is left as it is."""
    name, header = str(record["name"]), declared_name(record.get("statement", ""))
    return header if header and header != name and header.startswith(name) else name


def content_tag(record: Dict[str, Any]) -> str:
    """10 hex digits of what the record states: two records of one name that state different things get different tags"""
    return hashlib.sha256(str(record.get("statement", "")).encode("utf-8")).hexdigest()[:10]


def assign_refs(v1: List[Dict[str, Any]], names: Optional[List[str]] = None) -> List[str]:
    """one reference per version 1 record, in the records' order.

    `<library>:<name>` while that pair is unique in the dataset; `<library>:<name>~<tag>` when it is not, where the tag is the statement's digest, and `.2`, `.3` ... when
    even that ties (the same statement twice; the order is the source_url, then the proof's digest, so the same data always gives the same refs)."""
    names = names if names is not None else [r["name"] for r in v1]
    groups: Dict[Tuple[str, str], List[int]] = defaultdict(list)
    for i, r in enumerate(v1):
        groups[(r["library"], names[i])].append(i)
    refs: List[str] = [""] * len(v1)
    for (library, name), idx in groups.items():
        if len(idx) == 1:
            refs[idx[0]] = f"{library}:{name}"
            continue
        by_tag: Dict[str, List[int]] = defaultdict(list)
        for i in idx:
            by_tag[content_tag(v1[i])].append(i)
        for tag, same in by_tag.items():
            same.sort(key=lambda i: (str(v1[i].get("source_url")), hashlib.sha256(str(v1[i].get("proof")).encode("utf-8")).hexdigest()))
            for k, i in enumerate(same, 1):
                refs[i] = f"{library}:{name}~{tag}" + ("" if k == 1 else f".{k}")
    return refs


# ---------------------------------------------------------------------------------------------------------------- the two directions


def upgrade_dataset(
    v1: List[Dict[str, Any]], ids: Optional[Dict[Tuple[str, str, Optional[str]], str]] = None
) -> Tuple[List[Dict[str, Any]], Dict[str, Any]]:
    """version 1 rows -> version 2 rows, and a report.

    `ids` maps (library, name, module) to a statement id; module None means any module. A record gets an id from its own module's entry; from a module-less entry only when its (library, name)
    is not shared in the dataset (an id says what a statement is: it is not put on every record that merely has the same name, and `ids_skipped_shared` counts the records where that was refused)."""
    names = [repaired_name(r) for r in v1]
    refs = assign_refs(v1, names)
    ids = ids or {}
    out: List[Dict[str, Any]] = []
    matched = skipped = 0
    shared: Dict[Tuple[str, str], int] = defaultdict(int)
    for r, name in zip(v1, names):
        shared[(r["library"], name)] += 1
    for r, ref, name in zip(v1, refs, names):
        row: Dict[str, Any] = {"schema": SCHEMA, "ref": ref, "status": "trusted"}
        module = module_of(r.get("source_url"))
        ident = ids.get((r["library"], name, module)) if module else None
        any_module = ids.get((r["library"], name, None)) or ids.get((r["library"], r["name"], None))
        if ident is None and any_module is not None:
            if shared[(r["library"], name)] == 1:
                ident = any_module
            else:
                skipped += 1
        if ident is not None:
            row["id"] = ident
            matched += 1
        if name != r["name"]:
            row["legacy_name"] = r["name"]
        module = module_of(r.get("source_url"))
        if module is not None:
            row["module"] = module
        for key in V1_FIELDS:
            value = r.get(key)
            new_key = RENAMED_FIELD[1] if key == RENAMED_FIELD[0] else key
            if key == "headline":
                if value is True:
                    row["headline"] = True
            elif key == "name":
                row["name"] = name
            elif value is not None:
                row[new_key] = value
        out.append({k: row[k] for k in V2_FIELDS if k in row})
    return out, {
        "records": len(out),
        "with_id": matched,
        "ids_skipped_shared": skipped,
        "names_repaired": sum(1 for r in out if "legacy_name" in r),
        "refs_with_a_tag": sum(1 for r in out if "~" in r["ref"]),
        "modules": sum(1 for r in out if "module" in r),
    }


def downgrade(row: Dict[str, Any]) -> Dict[str, Any]:
    """one version 2 row -> the version 1 row it came from (every version 1 field, null where the row has none)"""
    out: Dict[str, Any] = {}
    for key in V1_FIELDS:
        if key == "headline":
            out[key] = row.get("headline") is True
        elif key == RENAMED_FIELD[0]:
            out[key] = row.get(RENAMED_FIELD[1])
        elif key == "name":
            out[key] = row.get("legacy_name", row.get("name"))
        else:
            out[key] = row.get(key)
    return out


def upgrade(record: Dict[str, Any]) -> Dict[str, Any]:
    """one version 1 record on its own. A lone record cannot know whether its name is shared with another record of the dataset, so its ref is the plain `<library>:<name>`:
    migrate the dataset (`upgrade_dataset`) to get the refs the release has."""
    return upgrade_dataset([record])[0][0]


# ---------------------------------------------------------------------------------------------------------------- the checks


def check(rows: List[Dict[str, Any]]) -> List[str]:
    problems: List[str] = []
    seen: Dict[str, int] = {}
    for i, r in enumerate(rows, 1):
        for k in V2_REQUIRED:
            if r.get(k) is None:
                problems.append(f"row {i}: missing {k}")
        extra = sorted(set(r) - set(V2_FIELDS))
        if extra:
            problems.append(f"row {i}: unknown fields {extra}")
        if r.get("schema") != SCHEMA:
            problems.append(f"row {i}: schema is {r.get('schema')!r}, not {SCHEMA}")
        ref = r.get("ref")
        if isinstance(ref, str):
            if not REF.match(ref):
                problems.append(f"row {i}: ref {ref!r} is not <library>:<name>")
            elif not ref.startswith(f"{r.get('library')}:{r.get('name')}"):
                problems.append(f"row {i}: ref {ref!r} does not start with its library and name")
            if ref in seen:
                problems.append(f"row {i}: ref {ref!r} already used by row {seen[ref]}")
            seen[ref] = i
        if "legacy_name" in r and not (r["legacy_name"] != r.get("name") and str(r.get("name", "")).startswith(r["legacy_name"])):
            problems.append(f"row {i}: legacy_name {r['legacy_name']!r} is not a proper prefix of the name {r.get('name')!r}")
        if "id" in r and not ISNAD_ID.match(str(r["id"])):
            problems.append(f"row {i}: id {r['id']!r} is not an isnad id")
        if "module" in r and module_of(r.get("source_url")) != r["module"]:
            problems.append(f"row {i}: module {r['module']!r} is not the module of the source_url")
        for k, v in r.items():
            if v is None or (k == "headline" and v is not True):
                problems.append(f"row {i}: {k} must be left out when it does not apply")
    return problems


# ---------------------------------------------------------------------------------------------------------------- resolving


class Resolution:
    """what a query names: status is exact, unique-name, ambiguous, candidates (a relative name that might be meant, never an answer) or not-found"""

    def __init__(self, status: str, query: str, records: List[Dict[str, Any]], candidates: List[str], note: str = ""):
        self.status, self.query, self.records, self.candidates, self.note = status, query, records, candidates, note

    def one(self) -> Dict[str, Any]:
        """the record, or an error saying why there is not exactly one"""
        if len(self.records) != 1:
            raise LookupError(f"{self.query!r}: {self.status}; {self.note}")
        return self.records[0]

    def __repr__(self) -> str:
        return f"Resolution({self.status}, {len(self.records)} record(s), candidates={self.candidates[:3]})"


class Index:
    """a version 2 dataset, searchable by every way anyone has named a theorem: version 2 reference, statement id, `library:name`, the plain version 1 name"""

    def __init__(self, rows: List[Dict[str, Any]]):
        self.rows = rows
        self.by_ref = {r["ref"]: r for r in rows}
        self.by_id: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        self.by_pair: Dict[Tuple[str, str], List[Dict[str, Any]]] = defaultdict(list)
        self.by_name: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        self.by_legacy: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        for r in rows:
            if "legacy_name" in r:
                self.by_legacy[r["legacy_name"]].append(r)
            if "id" in r:
                self.by_id[r["id"]].append(r)
            self.by_pair[(r["library"], r["name"])].append(r)
            self.by_name[r["name"]].append(r)

    def resolve(self, query: str, library: Optional[str] = None) -> Resolution:
        q = query.strip()
        if q in self.by_ref:
            return Resolution("exact", q, [self.by_ref[q]], [])
        if ISNAD_ID.match(q):
            hits = self.by_id.get(q, [])
            return Resolution(
                "exact" if hits else "not-found",
                q,
                list(hits),
                [r["ref"] for r in hits],
                "a statement id names every record that states it",
            )
        if ":" in q and "~" not in q:
            lib, _, name = q.partition(":")
            hits = self.by_pair.get((lib, name), []) + [r for r in self.by_legacy.get(name, []) if r["library"] == lib]
            return self._decide(q, hits)
        hits = self.by_name.get(q, []) + self.by_legacy.get(q, [])
        if library is not None:
            hits = [r for r in hits if r["library"] == library]
        if not hits and "." in q:
            # the dataset's names are as written in the source, relative to their namespace: `Nat.add_comm` is `add_comm` there. Never an answer, only candidates.
            parts = q.split(".")
            for k in range(1, len(parts)):
                tail = ".".join(parts[k:])
                near = [r for r in self.by_name.get(tail, []) if library is None or r["library"] == library]
                if near:
                    note = f"no record is named {q!r}; dataset names are relative to their namespace and these are named {tail!r}"
                    return Resolution("candidates", q, [], sorted(r["ref"] for r in near), note)
        res = self._decide(q, hits, plain=True)
        if q in self.by_legacy and not res.note.startswith("version 1"):
            res.note = ("version 1 cut some of these names at their first non-ASCII character; " + res.note).strip()
        return res

    @staticmethod
    def _decide(q: str, hits: List[Dict[str, Any]], plain: bool = False) -> Resolution:
        refs = sorted(r["ref"] for r in hits)
        if not hits:
            return Resolution(
                "not-found",
                q,
                [],
                [],
                "no record of that name: it was never in the dataset, or it was removed or renamed (diff says which)",
            )
        if len(hits) == 1:
            return Resolution(
                "unique-name" if plain else "exact", q, hits, refs, "" if hits[0]["name"] == q else f"the name is {hits[0]['name']!r}"
            )
        return Resolution("ambiguous", q, hits, refs, f"{len(hits)} records share it: name one of the candidates, or pass library=")

    def ref_of_v1(self, record: Dict[str, Any]) -> Optional[str]:
        """the version 2 reference of a version 1 record of this dataset"""
        for r in self.by_pair.get((record["library"], repaired_name(record)), []):
            if r["statement"] == record.get("statement") and r["source_url"] == record.get("source_url"):
                return r["ref"]
        return None


# ---------------------------------------------------------------------------------------------------------------- a version change


def shape_text(r: Dict[str, Any]) -> str:
    """a statement with the record's own name taken out and the white space collapsed: two records that state the same thing under different names have the same shape text"""
    return " ".join(str(r["statement"]).replace(str(r["name"]), "\u0000").split())


def content(r: Dict[str, Any]) -> Dict[str, Any]:
    """what a record says, without where it is and when it was promoted: the source_url (an upstream bump changes its commit), the module and the date are not content"""
    return {k: v for k, v in r.items() if k not in ("source_url", "module", "promoted_at")}


def classify(old: List[Dict[str, Any]], new: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """what happened to every record between two version 2 datasets (the migration record of docs/migration-support.md)

    unchanged   the same ref and the same content in the same module
    corrected   the same ref and statement, another proof, credit, licence or toolchain
    moved       the same ref and content, another module (the source_url and the promotion date are not content: an upstream bump is not a change)
    renamed     the old ref is gone and exactly one new ref (same library) has the same statement id, or, with no ids, the same statement text once the record's own name is taken out
    restated    the same ref or the same library and name, another statement
    removed     none of the above found a successor
    added       a ref that was not there
    A record is never guessed: where a successor is not exactly one, the record is `removed` and the new one `added`."""
    old_by, new_by = {r["ref"]: r for r in old}, {r["ref"]: r for r in new}
    out: List[Dict[str, Any]] = []
    gone = [r for r in old if r["ref"] not in new_by]
    fresh = {r["ref"]: r for r in new if r["ref"] not in old_by}

    def key_id(r: Dict[str, Any]) -> Optional[Tuple[str, str]]:
        return (r["library"], r["id"]) if "id" in r else None

    def key_text(r: Dict[str, Any]) -> Tuple[str, str]:
        return (r["library"], hashlib.sha256(shape_text(r).encode("utf-8")).hexdigest())

    by_id: Dict[Tuple[str, str], List[str]] = defaultdict(list)
    by_text: Dict[Tuple[str, str], List[str]] = defaultdict(list)
    by_pair: Dict[Tuple[str, str], List[str]] = defaultdict(list)
    for ref, r in fresh.items():
        if key_id(r):
            by_id[key_id(r)].append(ref)  # type: ignore[index]
        by_text[key_text(r)].append(ref)
        by_pair[(r["library"], r["name"])].append(ref)
    taken: set = set()
    for r in sorted(gone, key=lambda x: x["ref"]):
        successor, change = None, None
        cands = by_id.get(key_id(r), []) if key_id(r) else []  # type: ignore[arg-type]
        cands = [c for c in cands if c not in taken]
        if len(cands) == 1 and len(by_id[key_id(r)]) == 1:  # type: ignore[index]
            successor, change = cands[0], "renamed"
        if successor is None:
            cands = [c for c in by_text.get(key_text(r), []) if c not in taken]
            if len(cands) == 1 and len(by_text[key_text(r)]) == 1:
                successor, change = cands[0], "renamed"
        if successor is None:
            cands = [c for c in by_pair.get((r["library"], r["name"]), []) if c not in taken]
            if len(cands) == 1 and len(by_pair[(r["library"], r["name"])]) == 1:
                successor, change = cands[0], "restated"
        if successor is None:
            out.append({"old": r["ref"], "new": None, "change": "removed", "old_module": r.get("module"), "new_module": None})
        else:
            taken.add(successor)
            out.append(
                {
                    "old": r["ref"],
                    "new": successor,
                    "change": change,
                    "old_module": r.get("module"),
                    "new_module": fresh[successor].get("module"),
                }
            )
    for ref in sorted(set(old_by) & set(new_by)):
        a, b = old_by[ref], new_by[ref]
        if a["statement"] != b["statement"]:
            change = "restated"
        elif content(a) != content(b):
            change = "corrected"
        elif a.get("module") != b.get("module"):
            change = "moved"
        else:
            change = "unchanged"
        out.append({"old": ref, "new": ref, "change": change, "old_module": a.get("module"), "new_module": b.get("module")})
    for ref in sorted(set(fresh) - taken):
        out.append({"old": None, "new": ref, "change": "added", "old_module": None, "new_module": fresh[ref].get("module")})
    return out


def summarise(changes: List[Dict[str, Any]]) -> Dict[str, int]:
    counts = {c: 0 for c in CHANGES}
    for c in changes:
        counts[c["change"]] += 1
    return counts


# ---------------------------------------------------------------------------------------------------------------- Lean sources

# one pass over a Lean file that knows where code is: not in a comment (-- or nested /- -/), not in a string. A name is a run of identifier characters and dots, or a guillemet part.
TOKEN = re.compile(r"«[^»\n]*»|[^\W\d][\w'!?]*")


CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
RAW_STRING = re.compile(r'r(#*)"')


def code_spans(text: str) -> List[Tuple[int, int]]:
    """the (start, end) of every stretch of `text` that is code: not a comment (`--`, nested `/- -/`), not a string (`"..."`, raw `r#"..."#`) and not a character literal (`'"'`, `'\\n'`).
    The inside of an interpolated string (`s!"{x}"`) counts as string: a name there is neither rewritten nor reported."""
    spans: List[Tuple[int, int]] = []
    i, start, n = 0, 0, len(text)
    while i < n:
        two = text[i : i + 2]
        raw = RAW_STRING.match(text, i) if text[i] == "r" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")) else None
        if raw:
            spans.append((start, i))
            end = text.find('"' + raw.group(1), raw.end())
            i = start = n if end < 0 else end + 1 + len(raw.group(1))
        elif text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")) and CHAR_LITERAL.match(text, i):
            spans.append((start, i))
            i = start = CHAR_LITERAL.match(text, i).end()  # type: ignore[union-attr]
        elif two == "--":
            spans.append((start, i))
            j = text.find("\n", i)
            i = start = n if j < 0 else j
        elif two == "/-":
            spans.append((start, i))
            depth, i = 1, i + 2
            while i < n and depth:
                if text[i : i + 2] == "/-":
                    depth, i = depth + 1, i + 2
                elif text[i : i + 2] == "-/":
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            start = i
        elif text[i] == '"':
            spans.append((start, i))
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            start = i
        else:
            i += 1
    spans.append((start, n))
    return [s for s in spans if s[0] < s[1]]


def qualified_names(code: str, base: int) -> Iterable[Tuple[int, int, str]]:
    """every dotted name of a stretch of code: (start, end, name)"""
    for m in re.finditer(r"(?:" + TOKEN.pattern + r")(?:\.(?:" + TOKEN.pattern + r"))*", code):
        yield base + m.start(), base + m.end(), m.group(0)


def migrate_source(
    text: str, renames: Dict[str, str], gone: Optional[Dict[str, str]] = None, projections: bool = False
) -> Tuple[str, List[Dict[str, Any]]]:
    """rewrite a Lean source file: every code occurrence of a renamed name becomes its new name; occurrences of a removed or restated name are reported, never changed.

    `renames` maps old name -> new name; `gone` maps old name -> why it cannot be rewritten (`removed`, `restated`, `ambiguous`). Comments and strings are left alone.

    A dotted name that merely *begins* with a changed name (`old_name.symm`, `old_name.trans h`, `old_name.sub`) is not that name: it is the name used with a projection, or a different declaration under it,
    and a file cannot say which. It is reported as `unjudged` with its head and what happened to the head, and left as it is, unless `projections` is true, which rewrites the head of a renamed one
    (right for `.symm`, `.mp` and the like, wrong when `old_name.sub` is a declaration of its own). A name that only *ends* with a changed name (`Foo.old_name`, `x.old_name`) is not an occurrence. A use of a
    short name under `open` is not seen at all."""
    gone = gone or {}
    out: List[str] = []
    cursor = 0
    report: List[Dict[str, Any]] = []
    for start, end in code_spans(text):
        for s, e, name in qualified_names(text[start:end], start):
            line = text.count("\n", 0, s) + 1
            if name in renames:
                out.append(text[cursor:s])
                out.append(renames[name])
                cursor = e
                report.append({"line": line, "name": name, "action": "rewritten", "to": renames[name]})
            elif name in gone:
                report.append({"line": line, "name": name, "action": gone[name]})
            elif "." in name:
                parts = name.split(".")
                for k in range(len(parts) - 1, 0, -1):
                    head = ".".join(parts[:k])
                    if head in renames or head in gone:
                        if projections and head in renames:
                            out.append(text[cursor:s])
                            out.append(renames[head])
                            cursor = s + len(head)
                            report.append(
                                {"line": line, "name": name, "action": "rewritten", "to": renames[head] + name[len(head) :], "head": head}
                            )
                        else:
                            change = f"renamed to {renames[head]}" if head in renames else gone[head]
                            report.append({"line": line, "name": name, "action": "unjudged", "head": head, "head_change": change})
                        break
    out.append(text[cursor:])
    return "".join(out), report


# ---------------------------------------------------------------------------------------------------------------- the command line


def load_ids(path: Path) -> Dict[Tuple[str, str, Optional[str]], str]:
    """a TSV of `library<TAB>name<TAB>id` or `library<TAB>name<TAB>id<TAB>module` (an entry that is listed with two different ids has none)"""
    seen: Dict[Tuple[str, str, Optional[str]], set] = defaultdict(set)
    for line in path.read_text(encoding="utf-8").splitlines():
        parts = line.split("\t")
        if len(parts) >= 3 and ISNAD_ID.match(parts[2]):
            seen[(parts[0], parts[1], parts[3] if len(parts) > 3 and parts[3] else None)].add(parts[2])
    return {k: next(iter(v)) for k, v in seen.items() if len(v) == 1}


def short(ref: str) -> str:
    return ref.partition(":")[2].split("~")[0]


def name_maps(changes: List[Dict[str, Any]]) -> Tuple[Dict[str, str], Dict[str, str]]:
    """from a migration record: the names that can be rewritten (old -> new), and the names that cannot (old -> why).
    A name that several records carry (their refs differ by a tag) and that did not end up the same everywhere is `ambiguous`, never rewritten."""
    outcomes: Dict[str, set] = defaultdict(set)
    for c in changes:
        if c["change"] in ("renamed", "removed", "restated"):
            outcomes[short(c["old"])].add((c["change"], short(c["new"]) if c["new"] else None))
    renames: Dict[str, str] = {}
    gone: Dict[str, str] = {}
    for name, outs in outcomes.items():
        if len(outs) > 1:
            gone[name] = "ambiguous"
            continue
        change, new = next(iter(outs))
        if change == "renamed" and new and new != name:
            renames[name] = new
        elif change != "renamed":
            gone[name] = change
    return renames, gone


def checked_path(arg: Path) -> Path:
    """A path given on the command line, resolved; it must lie in the working directory or the temporary directory, so an argument cannot point a read or a write anywhere else
    (the rule of scripts/ci/axiom_scan.py; Sonar S8707)."""
    p = arg.resolve()
    roots = [Path.cwd(), Path(tempfile.gettempdir())] + ([Path(os.environ["RUNNER_TEMP"])] if os.environ.get("RUNNER_TEMP") else [])
    if not any(p.is_relative_to(r.resolve()) for r in roots):
        raise SystemExit(f"v2: {arg} is outside the working directory and the temporary directory")
    return p


def dataset_file(path: Path) -> Path:
    if path.is_dir():
        manifest = json.loads((path / "snapshot.json").read_text(encoding="utf-8"))
        return path / manifest["dataset"]["file"]
    return path


def is_dataset_path(p: Path) -> bool:
    return p.exists() and ((p.is_dir() and (p / "snapshot.json").is_file()) or p.suffix in (".jsonl", ".gz"))


def is_source_path(p: Path) -> bool:
    return p.exists() and (p.suffix == ".lean" or p.is_dir())


def migrate_dataset(path: Path, out: Optional[Path] = None, ids: Optional[Path] = None) -> Dict[str, Any]:
    """a snapshot directory or a dataset file -> the version 2 dataset (written to `out` when given); a version 2 dataset is returned unchanged"""
    rows = read_jsonl(dataset_file(path))
    if schema_of(rows) == SCHEMA:
        return {
            "kind": "dataset",
            "already": SCHEMA,
            "rows": rows,
            "report": {"records": len(rows), "note": "already version 2: returned unchanged"},
        }
    new, report = upgrade_dataset(rows, load_ids(ids) if ids else None)
    problems = check(new)
    if problems:
        raise ValueError("the upgraded dataset breaks its own invariants: " + "; ".join(problems[:5]))
    if out:
        write_jsonl(out, new)
    return {"kind": "dataset", "already": None, "rows": new, "report": report}


def patch_of(old_text: str, new_text: str, name: str) -> str:
    """the unified diff of one file, in the form `git apply` takes: a last line without a newline is marked, as git itself does"""
    out: List[str] = []
    for line in difflib.unified_diff(old_text.splitlines(True), new_text.splitlines(True), f"a/{name}", f"b/{name}"):
        out.append(line if line.endswith("\n") else line + "\n\\ No newline at end of file\n")
    return "".join(out)


def migrate_sources(path: Path, map_file: Optional[Path], projections: bool = False) -> Dict[str, Any]:
    """a Lean file or a directory of them -> for every file its report and the patch (nothing is written)"""
    if not map_file:
        raise ValueError("migrating Lean sources needs --map (the output of `v2.py diff`)")
    renames, gone = name_maps(read_jsonl(map_file))
    files = [path] if path.is_file() else sorted(path.rglob("*.lean"))
    results = []
    for f in files:
        old_text = f.read_text(encoding="utf-8")
        new_text, rep = migrate_source(old_text, renames, gone, projections)
        name = os.path.relpath(f)
        diff = patch_of(old_text, new_text, name)
        results.append({"file": str(f), "report": rep, "diff": diff, "new_text": new_text})
    return {"kind": "source", "files": results}


def resolve_name(query: str, dataset: Path, library: Optional[str] = None) -> Dict[str, Any]:
    """what a name, a ref or a statement id names in a version 2 dataset"""
    res = Index(read_jsonl(dataset)).resolve(query, library=library)
    return {"kind": "query", "status": res.status, "refs": [r["ref"] for r in res.records], "candidates": res.candidates, "note": res.note}


def migrate(
    source: Any,
    out: Any = None,
    ids: Any = None,
    map_file: Any = None,
    library: Optional[str] = None,
    projections: bool = False,
) -> Dict[str, Any]:
    """the helper: anything a consumer has of version 1 goes in, version 2 comes out; the result says what it did and what is left to a person.
    `source` is a snapshot directory, a dataset file, a Lean file or directory (paths, or strings naming them), or a name; the command line does the same with its paths checked first (`main`)."""
    p = source if isinstance(source, Path) else Path(str(source))

    def opt(v: Any) -> Optional[Path]:
        return None if v is None else (v if isinstance(v, Path) else Path(str(v)))

    if is_dataset_path(p):
        return migrate_dataset(p, opt(out), opt(ids))
    if is_source_path(p):
        return migrate_sources(p, opt(map_file), projections)
    if out is not None and Path(str(out)).exists():
        return resolve_name(str(source), Path(str(out)), library)
    raise ValueError(f"cannot tell what {source!r} is: a dataset or snapshot directory, a Lean file, or (with --out DATASET) a name")


def opt_path(value: Optional[str]) -> Optional[Path]:
    return checked_path(Path(value)) if value else None


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("migrate")
    m.add_argument("input")
    m.add_argument("--out")
    m.add_argument("--ids")
    m.add_argument("--map")
    m.add_argument("--library")
    m.add_argument(
        "--projections", action="store_true", help="Lean sources: also rewrite the head of `old_name.symm`-like names (docs/v2.md)"
    )
    c = sub.add_parser("check")
    c.add_argument("dataset")
    d = sub.add_parser("diff")
    d.add_argument("old")
    d.add_argument("new")
    d.add_argument("--out")
    a = ap.parse_args(argv)
    if a.cmd == "migrate":
        # every path is resolved and checked here, before anything is read or written; a name is not a path
        target = Path(a.input)
        if is_dataset_path(target):
            res = migrate_dataset(checked_path(target), opt_path(a.out), opt_path(a.ids))
        elif is_source_path(target):
            res = migrate_sources(checked_path(target), opt_path(a.map), a.projections)
        elif a.out and Path(a.out).exists():
            res = resolve_name(a.input, checked_path(Path(a.out)), a.library)
        else:
            raise SystemExit(
                f"v2: cannot tell what {a.input!r} is: a dataset or snapshot directory, a Lean file, or (with --out DATASET) a name"
            )
        if res["kind"] == "source":
            # the sources are not written: the change is a patch on stdout (`... | git apply`), the report is on stderr
            sys.stdout.write("".join(f["diff"] for f in res["files"]))
            print(json.dumps([{"file": f["file"], "report": f["report"]} for f in res["files"]], indent=1, sort_keys=True), file=sys.stderr)
            return 0
        print(json.dumps({k: v for k, v in res.items() if k != "rows"}, indent=1, sort_keys=True))
        return 0
    if a.cmd == "check":
        rows = read_jsonl(dataset_file(checked_path(Path(a.dataset))))
        problems = check(rows)
        for x in problems[:50]:
            print(x)
        print(f"{len(rows)} rows, {len(problems)} problem(s)")
        return 1 if problems else 0
    old, new = read_jsonl(dataset_file(checked_path(Path(a.old)))), read_jsonl(dataset_file(checked_path(Path(a.new))))
    if schema_of(old) == 1:
        old, _ = upgrade_dataset(old)
    if schema_of(new) == 1:
        new, _ = upgrade_dataset(new)
    changes = classify(old, new)
    if a.out:
        write_jsonl(checked_path(Path(a.out)), changes)
    print(json.dumps(summarise(changes), sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
