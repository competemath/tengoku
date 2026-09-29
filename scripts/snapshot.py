#!/usr/bin/env python3
"""snapshot.py --out DIR — a citable snapshot of the library: the dataset and its manifest.

Writes DIR/tengoku-dataset.jsonl.gz (one line per trusted record: what it states, its proof, where it came from,
its licence and credit; retracted records left out, corrected credits applied) and DIR/snapshot.json (the commit,
toolchain, counts per library and the dataset's sha256). The snapshot workflow publishes both as a dated release,
so a paper can cite exactly the library it used."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

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


def dataset(root: Path) -> tuple[list[dict], dict[str, dict[str, int]]]:
    sources = json.loads((root / "schemas" / "sources.json").read_text(encoding="utf-8"))
    licences = sources.get("licences", {})
    records: list[dict] = []
    counts: dict[str, dict[str, int]] = {}
    for tier in ("trusted", "staging", "tentative"):
        for library, files in library_files(root, tier).items():
            retracted, corrected, kept = set(), {}, []
            for f in files:
                for r in lines(f):
                    if "tombstone" in r:
                        retracted.add(r["tombstone"])
                    elif "credit_correction" in r:  # the newest by date, whatever file it is in
                        name, at = r["credit_correction"], str(r.get("at", ""))
                        if name not in corrected or at >= corrected[name][0]:
                            corrected[name] = (at, r.get("credit"), r.get("evidence"))
                    elif "tombstone_note" not in r and "name" in r:
                        kept.append(r)
            live = [r for r in kept if r["name"] not in retracted]
            counts.setdefault(library, {})[tier] = len(live)
            if tier != "trusted":
                continue
            for r in live:
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
                }
                if evidence:
                    row["credit_corrected_evidence"] = evidence
                if r.get("headline") is True:
                    row["headline"] = True
                if r.get("upstream"):
                    row["upstream"] = r["upstream"]
                records.append(row)
    return records, counts


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--root", default=str(ROOT))
    args = ap.parse_args()
    root, out = Path(args.root), Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    records, counts = dataset(root)
    text = "".join(
        json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in sorted(records, key=lambda r: (r["library"], r["name"]))
    )
    raw = text.encode("utf-8")
    path = out / "tengoku-dataset.jsonl.gz"  # the file the release publishes, and the one the manifest hashes
    path.write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))  # mtime 0: the same records give the same bytes
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True).stdout.strip() or None
    toolchain = (root / "lean-toolchain").read_text().strip() if (root / "lean-toolchain").exists() else None
    manifest = {
        "snapshot": time.strftime("%Y-%m-%d", time.gmtime()),
        "commit": commit,
        "toolchain": toolchain,
        "dataset": {
            "file": path.name,
            "records": len(records),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "uncompressed_sha256": hashlib.sha256(raw).hexdigest(),
        },
        "libraries": {k: counts[k] for k in sorted(counts)},
        "totals": {t: sum(c.get(t, 0) for c in counts.values()) for t in ("trusted", "staging", "tentative")},
    }
    (out / "snapshot.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"snapshot {manifest['snapshot']}: {len(records)} trusted records, sha256 {manifest['dataset']['sha256'][:16]}…")


if __name__ == "__main__":
    main()
