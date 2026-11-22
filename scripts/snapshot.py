#!/usr/bin/env python3
"""snapshot.py --out DIR [--previous PREV] — a citable snapshot of the library: the dataset and its manifest.

Writes DIR/tengoku-dataset.jsonl.gz (one line per trusted record: what it states, its proof, where it came from,
its licence and credit; retracted records left out, corrected credits applied) and DIR/snapshot.json (the version,
date, commit, toolchain, counts per library, the record fields and the dataset's sha256). The snapshot workflow
publishes both as the release vX.Y.Z, so a paper can cite exactly the library it used. With --notes it also writes
the release notes: what changed since the previous release, and what upgrading means.

The version is decided by comparing with the previous release (PREV holds its snapshot.json and dataset), never
by hand:
  X (major)  the toolchain changed, or a field was removed from the records: whoever compiles or reads the dataset
             has to act
  Y (minor)  theorems were added (new or newly trusted), or records gained a field
  Z (patch)  only corrections: retractions, credit corrections, fixes to existing records
No change to the dataset or the toolchain: no new version (DIR/unchanged is written and the workflow publishes
nothing). The first release is 1.0.0."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import v2  # noqa: E402  (the dataset's schema 2 and the migration from schema 1: docs/v2.md)

ROOT = Path(__file__).resolve().parents[1]
CREDIT_RE = re.compile(r"^\s*(Authors?:.*)$", re.M)


def lines(p: Path):
    for line in p.read_text(encoding="utf-8").splitlines():
        if line.strip():
            yield json.loads(line)


def licence_of(source_url: str, licences: dict[str, str]) -> str | None:
    best = max((prefix for prefix in licences if source_url.startswith(prefix)), key=len, default=None)
    return licences[best] if best else None


def credit_of(statement: str) -> str | None:
    doc = re.search(r"/--(.*?)-/", statement, re.S)  # the docstring, even after a leading ordinary comment
    found = CREDIT_RE.findall(doc.group(1)) if doc else []
    return " ".join(c.strip() for c in found) or None


def library_files(root: Path, tier: str) -> dict[str, list[Path]]:
    """library -> its files in data/<tier>/ (the flat file and any per-PR files)."""
    out: dict[str, list[Path]] = {}
    base = root / "data" / tier
    if not base.is_dir():
        return out
    for f in sorted(base.glob("*.jsonl")):
        out.setdefault(f.stem, []).append(f)
    for d in sorted(p for p in base.iterdir() if p.is_dir()):
        out.setdefault(d.name, []).extend(sorted(d.glob("*.jsonl")))
    return out


# every row has every field (null or false when it does not apply), so the fields change only when this code does:
# a release's version compares them
FIELDS = (
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


def load_licences(root: Path) -> dict[str, str]:
    """source_url prefix -> licence, from the registry"""
    return json.loads((root / "schemas" / "sources.json").read_text(encoding="utf-8")).get("licences", {})


def command_words(root: Path) -> frozenset[str]:
    """the words that begin a command in a module of the tree (schemas/command-keywords.json: the content gate lets a word at column 0 begin a command only if it is one of these)"""
    return frozenset(json.loads((root / "schemas" / "command-keywords.json").read_text(encoding="utf-8"))["commands"])


def starts_command(line: str, words: frozenset[str]) -> bool:
    """a line that begins a command: it starts at column 0 with a command keyword, an attribute list (`@[`) or a doc comment"""
    if not line or line[0].isspace():
        return False
    if line.startswith(("@[", "/--", "/-!")):
        return True
    m = re.match(r"«[^»]*»|[#A-Za-z_][^\s(\[{:⟨]*", line)
    return bool(m) and m.group(0) in words


def comment_end(text: str, i: int) -> int:
    """the index just after the block comment that opens at `i` (they nest); the end of the text when it never closes"""
    depth, n = 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif text.startswith("-/", i):
            depth, i = depth - 1, i + 2
            if depth == 0:
                return i
        else:
            i += 1
    return n


ISNAD_TAG = re.compile(r"@isnad1 id=(\S+) from=\S+ src=\S+ shape=\S+ vocab=\S+\s*-/\Z")


def locate_header(text: str, statement: str) -> int | None:
    """where the header `statement` begins in the text of its module: it must be there once and begin a line (a header found twice, or in the middle of a line, may be another declaration or a comment)"""
    start = text.find(statement)
    if start < 0 or text.find(statement, start + 1) >= 0 or text[text.rfind("\n", 0, start) + 1 : start].strip():
        return None
    return start


def declaration_tag(text: str, statement: str) -> str | None:
    """the statement id in the isnad tag of the docstring that ends right above the header (docs/isnad.md: the tag, `@isnad1 id=... from=... src=... shape=... vocab=...`, is the last line of a theorem's
    docstring). None when the header is not found as `locate_header` finds it, when nothing but white space does not separate the docstring from it (another declaration's docstring is not this one's), when
    the docstring has no tag as its last line, or when the id is not shaped like one. The tag was written by the tag gate from the compiled module (docs/pr-classes.md, section 7); it is read here, not recomputed."""
    start = locate_header(text, statement)
    if start is None:
        return None
    before = text[:start].rstrip()
    k = before.rfind("/--") if before.endswith("-/") else -1
    if k < 0 or "-/" in before[k:-2]:
        return None
    m = ISNAD_TAG.search(before[k:])
    return m.group(1) if m and v2.ISNAD_ID.match(m.group(1)) else None


def declaration_proof(text: str, statement: str, words: frozenset[str]) -> str | None:
    """the proof of the declaration whose header is `statement`, read from the text of its module: from the `:=` (or `where`) to the end of the declaration. None when it cannot be said without guessing.

    The manifest keeps a theorem's header exactly as the module has it, so the header is found in the module's text. It must be there once and begin a line (a header found twice, or in the middle of a
    line, may be another declaration or a comment); what follows it is the proof, up to the next command. A command begins where the tree's own gate says it does (`starts_command`): at column 0 with
    a command keyword. Any other word at column 0, an indented line and a `--` comment inside the proof belong to the proof; comments after its last line (a `--` or a block comment at column 0) do not.
    A header that has no `:=` after it (equation-style definitions keep their match arms in the header) has no proof text: the module has the whole declaration."""
    start = locate_header(text, statement)
    if start is None:
        return None
    i = start + len(statement)
    pos = text.find("\n", i)
    end = len(text) if pos < 0 else pos  # the rest of the header's last line is the beginning of the proof
    while pos >= 0:
        nxt = pos + 1
        eol = text.find("\n", nxt)
        line_end = len(text) if eol < 0 else eol
        line = text[nxt:line_end]
        if not line.strip() or line.startswith("--"):
            pass
        elif line.startswith("/-") and not line.startswith(("/--", "/-!")):
            close = comment_end(text, nxt)
            eol = text.find("\n", close)
            # a block comment at column 0 is skipped, and not part of the proof unless the proof goes on after it: on the line where it closes, a command
            # begins the next declaration (`/- note -/ theorem bar ...`), any other code goes on with the proof above
            rest = text[close : len(text) if eol < 0 else eol]
            if rest.strip():
                if starts_command(rest.lstrip(), words):
                    break
                end = len(text) if eol < 0 else eol
        elif line[0].isspace():
            end = line_end
        elif starts_command(line, words):
            break
        else:
            end = line_end  # a word that is not a command continues the command above
        pos = eol
    proof = text[i:end].strip()
    return proof if proof.startswith((":=", "where")) else None


def module_text(root: Path, module: str, cache: dict[str, str | None]) -> str | None:
    """the source of a module of the tree (`Tengoku.A.B` is Tengoku/A/B.lean), or None when the file is not there"""
    if module not in cache:
        f = root.joinpath(*module.split(".")).with_name(module.split(".")[-1] + ".lean")
        cache.clear()  # the manifest lists a library module by module: one file at a time is enough
        cache[module] = f.read_text(encoding="utf-8") if f.is_file() else None
    return cache[module]


def intake_rows(root: Path, licences: dict[str, str], ids: dict | None = None, proofs: bool = True) -> tuple[list[dict], dict[str, int]]:
    """schema 2 rows for the theorems that arrived in the tree as modules: one per line of `data/intake/<library>/manifest.jsonl` (docs/v2.md, "The theorems that arrived as modules").

    The manifest of a library is exactly what the tree holds of it: a raze removes the lines of the modules it removes (docs/pr-classes.md, section 8), so nothing is retracted here. `ids` is the
    optional table of `v2.load_ids`; an id goes to the theorem it names by its tree module, its upstream module or no module at all (a library's names are unique, so a name names one theorem).
    With `proofs` the modules are read: a row gets the proof text `declaration_proof` reads out of its module, where it can be read (a row without one has the module, `tree_module`, for its proof), and the
    statement id `declaration_tag` reads from the isnad tag of its docstring (the table `ids` wins where both have one)."""
    rows: list[dict] = []
    counts: dict[str, int] = {}
    base = root / "data" / "intake"
    words: frozenset[str] | None = None  # read when the first manifest is: a tree with no intake needs no keyword list
    cache: dict[str, str | None] = {}
    for d in sorted(p for p in base.iterdir() if p.is_dir()) if base.is_dir() else []:
        manifest = d / "manifest.jsonl"
        if not manifest.is_file():
            continue
        entries = list(lines(manifest))
        if proofs and words is None:
            words = command_words(root)
        order = sorted(
            range(len(entries)), key=lambda k: str(entries[k].get("module"))
        )  # a module's theorems together: its file is read once (the rows keep the manifest's order)
        proof_of: dict[int, str | None] = {}
        tag_of: dict[int, str | None] = {}
        for k in order if proofs else []:
            m = entries[k]
            text = module_text(root, str(m.get("module")), cache)
            proof_of[k] = declaration_proof(text, str(m.get("statement")), words) if text is not None else None
            tag_of[k] = declaration_tag(text, str(m.get("statement"))) if text is not None else None
        for k, m in enumerate(entries):
            library = m.get("library") or d.name
            keys = (
                (library, m.get("name"), m.get("module")),
                (library, m.get("name"), v2.module_of(m.get("source_url"))),
                (library, m.get("name"), None),
            )
            ident = next((ids[x] for x in keys if ids and x in ids), None) or tag_of.get(
                k
            )  # a table the caller gives wins over the tag in the module
            rows.append(v2.intake_row(m, licence_of(str(m.get("source_url", "")), licences), ident, proof_of.get(k)))
            counts[library] = counts.get(library, 0) + 1
    return rows, counts


def dataset(root: Path) -> tuple[list[dict], dict[str, dict[str, int]]]:
    licences = load_licences(root)
    records: list[dict] = []
    counts: dict[str, dict[str, int]] = {}
    for tier in ("trusted", "staging", "tentative"):
        # a library's records can be spread over several files (Mathlib's are data/trusted/mathlib-*.jsonl), so the
        # retractions and corrections of a tier apply across all its files, and a record counts for the library it
        # names (the file's name only when it names none)
        retracted, corrected, kept = set(), {}, []
        for stem, files in library_files(root, tier).items():
            for f in files:
                for r in lines(f):
                    if "tombstone" in r:
                        retracted.add(r["tombstone"])
                    elif "credit_correction" in r:  # the newest by date, whatever file it is in
                        name, at = r["credit_correction"], str(r.get("at", ""))
                        if name not in corrected or at >= corrected[name][0]:
                            corrected[name] = (at, r.get("credit"), r.get("evidence"))
                    elif "tombstone_note" not in r and "name" in r:
                        kept.append((r.get("library") or stem, r))
        for library, r in kept:
            if r["name"] in retracted:
                continue
            counts.setdefault(library, {})
            counts[library][tier] = counts[library].get(tier, 0) + 1
            if tier != "trusted":
                continue
            _, credit, evidence = corrected.get(r["name"], (None, credit_of(str(r.get("statement", ""))), None))
            row = {
                "name": r["name"],
                "library": library,
                "statement": r.get("statement"),
                "proof": r.get("proof"),
                "source_url": r.get("source_url"),
                "licence": licence_of(str(r.get("source_url", "")), licences),
                "credit": credit,
                "toolchain": r.get("toolchain"),
                "promoted_at": r.get("promoted_at"),
                "credit_corrected_evidence": evidence or None,
                "headline": r.get("headline") is True,
                "upstream": r.get("upstream") or None,
            }
            assert tuple(row) == FIELDS
            records.append(row)
    return records, counts


FIRST_VERSION = "1.0.0"


def key_of(row: dict) -> str:
    """what identifies a record across releases: its `ref` (schema 2), or, for schema 1, its name (which several records can share)"""
    return row.get("ref") or row["name"]


def previous_release(prev: Path | None, schema: int = 1) -> tuple[dict, dict[str, dict]] | None:
    """The previous release's manifest and its records by key, or None when there is none. A schema 1 release is read as schema 2 when the release being made is schema 2,
    so that the two are compared record by record (docs/v2.md); the other way round is refused: a dataset does not go back to schema 1."""
    if prev is None or not (prev / "snapshot.json").is_file():
        return None
    manifest = json.loads((prev / "snapshot.json").read_text(encoding="utf-8"))
    raw = gzip.decompress((prev / manifest["dataset"]["file"]).read_bytes()).decode("utf-8")
    rows = [json.loads(x) for x in raw.splitlines() if x.strip()]
    old_schema = manifest.get("schema", 1)
    if old_schema > schema:
        raise SystemExit(f"the previous release is schema {old_schema}: a dataset does not go back to schema {schema}")
    if old_schema < schema:
        rows, _ = v2.upgrade_dataset(rows)
    return manifest, {key_of(r): r for r in rows}


def next_version(
    previous: tuple[dict, dict[str, dict]] | None, names: set[str], fields: list[str], toolchain: str | None, raw_sha: str
) -> str | None:
    """The version of this snapshot, or None when nothing changed since the previous release (module docstring)."""
    if previous is None:
        return FIRST_VERSION
    old, old_rows = previous
    old_names = set(old_rows)
    major, minor, patch = (int(x) for x in old["version"].split("."))
    if old.get("toolchain") != toolchain or set(old.get("fields", [])) - set(fields):
        return f"{major + 1}.0.0"
    if old["dataset"].get("uncompressed_sha256") == raw_sha:
        return None
    if names - old_names or set(fields) - set(old.get("fields", [])):
        return f"{major}.{minor + 1}.0"
    return f"{major}.{minor}.{patch + 1}"


def by_library(rows: list[dict], top: int = 5) -> str:
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["library"]] = counts.get(r["library"], 0) + 1
    ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
    shown = ", ".join(f"{lib} {n:,}" for lib, n in ranked[:top])
    return shown + (f", and {len(ranked) - top} more libraries" if len(ranked) > top else "")


def release_notes(
    version: str,
    previous: tuple[dict, dict[str, dict]] | None,
    records: list[dict],
    toolchain: str | None,
    fields: list[str],
    schema: int = 1,
) -> str:
    """The release notes: what changed since the previous release, and what upgrading means. Written from the same
    comparison that chose the version number, so the notes and the number always agree."""
    if previous is None:
        return (
            f"## What is in v{version}\n\n"
            f"The first release: {len(records):,} trusted theorems from {len({r['library'] for r in records})} libraries "
            f"({by_library(records)}), on `{toolchain}`.\n\n"
            "## Upgrade impact\n\nNone: this is the first release.\n"
        )
    old, old_rows = previous
    rows = {key_of(r): r for r in records}
    renamed: list[dict] = []
    if schema == 2:
        # a ref depends on the whole dataset (a second record called `foo` gives both a tag), so the two releases are compared by what each record is, not by the string of its ref
        changes = v2.classify(list(old_rows.values()), records)
        added = [rows[c["new"]] for c in changes if c["change"] == "added"]
        retracted = sorted(c["old"] for c in changes if c["change"] == "removed")
        renamed = [c for c in changes if c["change"] == "renamed"]
        corrected = sorted(c["new"] for c in changes if c["change"] in ("corrected", "restated", "moved"))
    else:
        added = [rows[n] for n in sorted(set(rows) - set(old_rows))]
        retracted = sorted(set(old_rows) - set(rows))
        corrected = sorted(n for n in set(rows) & set(old_rows) if rows[n] != old_rows[n])
    lines = [f"## What changed since v{old['version']}", ""]
    lines.append(f"- **Added:** {len(added):,} trusted theorems" + (f" ({by_library(added)})." if added else "."))
    lines.append(
        f"- **Retracted:** {len(retracted):,}"
        + (f": {', '.join(f'`{n}`' for n in retracted[:10])}{' …' if len(retracted) > 10 else ''}." if retracted else ".")
    )
    lines.append(
        f"- **Corrected:** {len(corrected):,} existing theorems (a credit or another field changed)"
        + ("." if not corrected else f", e.g. `{corrected[0]}`.")
    )
    if renamed:
        lines.append(
            f"- **Renamed:** {len(renamed):,} records changed their `ref` (the same statement under another name, or the same name that is now shared): "
            f"`{renamed[0]['old']}` → `{renamed[0]['new']}`" + (", for example." if len(renamed) > 1 else ".")
        )
    if old.get("toolchain") != toolchain:
        lines.append(f"- **Toolchain:** `{old.get('toolchain')}` → `{toolchain}`.")
    else:
        lines.append(f"- **Toolchain:** unchanged, `{toolchain}`.")
    gone, new = sorted(set(old.get("fields", [])) - set(fields)), sorted(set(fields) - set(old.get("fields", [])))
    lines.append(
        "- **Record fields:** "
        + (
            "; ".join(
                x
                for x in (
                    f"added {', '.join(f'`{f}`' for f in new)}" if new else "",
                    f"removed {', '.join(f'`{f}`' for f in gone)}" if gone else "",
                )
                if x
            )
            or "unchanged"
        )
        + "."
    )
    lines += ["", "## Upgrade impact", ""]
    if version.endswith(".0.0"):
        why = []
        if old.get("toolchain") != toolchain:
            why.append(f"the Lean toolchain changed: anything built against v{old['version']} must be rebuilt on `{toolchain}`")
        if old.get("schema", 1) != schema:
            why.append(
                f"the dataset's schema changed from {old.get('schema', 1)} to {schema}: every record now has a `ref`, version 1's cut names are repaired and null fields are left out; "
                "`scripts/v2.py migrate` turns a version 1 dataset (or a name, or a Lean file) into the new one, and `docs/v2.md` says what each reader has to do"
            )
        tree = sum(1 for r in records if "tree_module" in r)
        if tree:
            read = sum(1 for r in records if "tree_module" in r and "proof" in r)
            tagged = sum(1 for r in records if "tree_module" in r and "id" in r)
            why.append(
                f"the dataset now holds every trusted theorem of the tree, {tree:,} of them theorems of libraries that arrived as modules: {read:,} of those rows have a `proof` read "
                "from their module, the others have none (their proof is the module `tree_module`, in the source release of the same version), "
                f"{tagged:,} have an `id`, the statement id of the isnad tag in their module's docstring, and all carry `via`, how Gate 2 related the statement to the original's"
            )
        if gone:
            why.append(f"record fields were removed or renamed ({', '.join(gone)}): code reading the dataset must stop expecting them")
        lines.append("Major version: " + "; ".join(why) + ".")
    elif version.endswith(".0"):
        what = []
        if added:
            what.append(f"{len(added):,} theorems were added")
        if new:
            what.append(f"records gained {', '.join(f'`{f}`' for f in new)}")
        lines.append(
            "Minor version: "
            + " and ".join(what)
            + "; nothing is renamed and no field is removed, so upgrading is safe"
            + (", except that the retracted theorems above are gone." if retracted else ".")
        )
    else:
        lines.append(
            "Patch: corrections only (retractions and credit corrections); no theorem was added"
            + (". Check that you do not rely on the retracted theorems above." if retracted else ".")
        )
    return "\n".join(lines) + "\n"


def pick_root(arg: str | None) -> Path:
    """the repository to read: the one this script is in unless --root names another, which must lie in the working or temporary directory"""
    return v2.checked_path(Path(arg)) if arg else ROOT


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--root", help="the repository to read (default: the one this script is in)")
    ap.add_argument("--previous", help="a directory with the previous release's snapshot.json and dataset")
    ap.add_argument("--notes", help="where to write the release notes (markdown); kept out of --out, which is published")
    ap.add_argument(
        "--schema", type=int, choices=(1, 2), default=1, help="the dataset's schema (docs/v2.md); 1 until a maintainer cuts 2.0.0"
    )
    ap.add_argument("--ids", help="schema 2: a TSV of library, name, isnad id; a record listed there carries the id")
    args = ap.parse_args()
    root, out = pick_root(args.root), v2.checked_path(Path(args.out))
    out.mkdir(parents=True, exist_ok=True)
    records, counts = dataset(root)
    if args.schema == 2:
        ids = v2.load_ids(v2.checked_path(Path(args.ids))) if args.ids else None
        records, _ = v2.upgrade_dataset(records, ids)
        tree_rows, tree_counts = intake_rows(
            root, load_licences(root), ids
        )  # schema 2 holds every trusted theorem of the tree: the intake libraries too
        records += tree_rows
        tree_n, tree_proofs, tree_ids = len(tree_rows), sum(1 for r in tree_rows if "proof" in r), sum(1 for r in tree_rows if "id" in r)
        for library, n in tree_counts.items():
            counts.setdefault(library, {})["intake"] = n
        problems = v2.check(records)
        if problems:
            raise SystemExit("the schema 2 dataset breaks its own invariants: " + "; ".join(problems[:5]))
    order = (lambda r: (r["library"], r["ref"])) if args.schema == 2 else (lambda r: (r["library"], r["name"]))
    text = "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in sorted(records, key=order))
    raw = text.encode("utf-8")
    path = out / "tengoku-dataset.jsonl.gz"  # the file the release publishes, and the one the manifest hashes
    path.write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))  # mtime 0: the same records give the same bytes
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True).stdout.strip() or None
    toolchain = (root / "lean-toolchain").read_text().strip() if (root / "lean-toolchain").exists() else None
    fields = sorted(v2.V2_FIELDS if args.schema == 2 else FIELDS)  # not read from the rows: a release with no records keeps the same fields
    previous = previous_release(v2.checked_path(Path(args.previous)) if args.previous else None, args.schema)
    names = {key_of(r) for r in records}
    if args.schema == 2 and previous is not None:
        old_refs = set(previous[1])
        names = old_refs | {
            c["new"] for c in v2.classify(list(previous[1].values()), records) if c["change"] == "added"
        }  # only what is really new counts as added
    version = next_version(
        previous,
        names,
        fields,
        toolchain,
        hashlib.sha256(raw).hexdigest(),
    )
    if version is None:
        (out / "unchanged").write_text("the dataset and toolchain are those of the previous release\n")
        print("unchanged since the previous release: no new version")
        return
    manifest = {
        "version": version,
        "date": time.strftime("%Y-%m-%d", time.gmtime()),
        "commit": commit,
        "toolchain": toolchain,
        "fields": fields,
        **({"schema": 2, "required": sorted(v2.V2_REQUIRED)} if args.schema == 2 else {}),
        "dataset": {
            "file": path.name,
            "records": len(records),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "uncompressed_sha256": hashlib.sha256(raw).hexdigest(),
        },
        **({"tree": {"theorems": tree_n, "with_proof": tree_proofs, "with_id": tree_ids}} if args.schema == 2 else {}),
        "libraries": {k: counts[k] for k in sorted(counts)},
        "totals": {
            t: sum(c.get(t, 0) for c in counts.values())
            for t in (("trusted", "intake", "staging", "tentative") if args.schema == 2 else ("trusted", "staging", "tentative"))
        },
    }
    (out / "snapshot.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.notes:
        v2.checked_path(Path(args.notes)).write_text(
            release_notes(version, previous, records, toolchain, fields, args.schema), encoding="utf-8"
        )
    print(f"v{version} ({manifest['date']}): {len(records)} trusted records, sha256 {manifest['dataset']['sha256'][:16]}…")


if __name__ == "__main__":
    main()
