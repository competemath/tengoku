#!/usr/bin/env python3
"""independent_check.py - the independent check (.github/workflows/independent-check.yml) in shards. Standard library only.

  independent_check.py plan  --all Tengoku/All.lean (--tree-json API_TREE.json | --sizes LS_TREE.txt) --paths DATA_PATHS.txt --shards N --out plan.json --matrix matrix.json [--commit SHA]
  independent_check.py merge --plan plan.json --reports DIR --commit SHA --lean4export-commit X --nanoda-commit Y --run URL --out independent-check.json

One `lean4export Tengoku.All` of the whole tree is one process that writes about 13,000 lines a second: 4 h 04 min for 196.6 million lines on 2026-10-12, the last time the check passed. The tree has grown
since, and the job's 350 minutes ran out in the export on every night from 16 November. The tree is cut into SHARDS, each a job of its own:

  shard 0   the seeded root `Tengoku` (all of Lean core and the seed) and the compiled libraries of the tier files (`Tengoku.EquationalTheories`), and the audit of the records of every library of
            `data/trusted` (those whose libraries have no modules in the tree are counted, by library, as before);
  shard 1.. the libraries that arrived as modules (`data/intake`), balanced by the size of their sources; a shard exports the libraries it was given, and the part of the seed they import.

`lean4export` of a set of roots writes every constant of the environment they make, so the union of the shards holds every constant `Tengoku.All` has (`plan` checks that the roots of the shards are exactly the
imports of `Tengoku/All.lean`, each once). Each shard is checked by nanoda on its own export and by `axiom_scan.py` (every declaration of it for sorryAx and axioms outside the prelude; the records of its own
libraries for the standard three). The libraries of the shards are disjoint, so their record audits add up. `merge` joins the shards' reports into the one report a release reads
(`independent-check.json`: `commit`, `axiom_scan.passed`, ...), and refuses to write it unless every shard is there once, for this commit, by the pinned tools, and passed.
"""

from __future__ import annotations

import argparse
import datetime
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

IMPORT = re.compile(r"^import (Tengoku(?:\.[A-Za-z0-9_]+)?)\s*$")
ROOT = re.compile(r"^Tengoku(?:\.[A-Za-z0-9_]+)?$")
LIBRARY = re.compile(r"^[A-Za-z0-9._-]+$")


def pascal(s: str) -> str:
    """equational-theories -> EquationalTheories, as scripts/ci/_git.py names a library's modules (and axiom_scan.py does)"""
    return "".join(w[:1].upper() + w[1:] for w in s.replace("_", "-").split("-") if w)


def all_roots(text: str) -> list[str]:
    """the modules Tengoku/All.lean imports: the seeded root `Tengoku` and `Tengoku.<Library>` for every library"""
    return [m.group(1) for ln in text.splitlines() if (m := IMPORT.match(ln))]


def sizes_by_namespace(ls_tree: str) -> dict[str, int]:
    """bytes of Lean source per `Tengoku/<Namespace>` from `git ls-tree -r -l <commit> -- Tengoku` (`<mode> blob <sha> <size>\\t<path>`); the umbrella `Tengoku/<Namespace>.lean` counts for its namespace"""
    out: dict[str, int] = defaultdict(int)
    for line in ls_tree.splitlines():
        meta, _, path = line.partition("\t")
        parts = meta.split()
        if len(parts) != 4 or parts[1] != "blob" or not path.startswith("Tengoku/") or not parts[3].isdigit():
            continue
        ns = path[len("Tengoku/") :].split("/", 1)[0]
        out[ns[: -len(".lean")] if ns.endswith(".lean") else ns] += int(parts[3])
    return dict(out)


def sizes_from_api(doc: dict) -> dict[str, int]:
    """bytes of Lean source per `Tengoku/<Namespace>` from the GitHub API's listing of the `Tengoku` tree (`gh api repos/<repo>/git/trees/<tree>?recursive=1`: paths relative to Tengoku/). `git ls-tree -l`
    would do, but in the blobless clone the job makes it fetches the blobs one at a time (48,000 of them) to read their sizes; the API has the sizes. A truncated listing is refused: a library's size would be wrong."""
    if doc.get("truncated"):
        raise SystemExit("the GitHub API's listing of the Tengoku tree is truncated: the sizes of the libraries are not all known")
    out: dict[str, int] = defaultdict(int)
    for e in doc.get("tree", []):
        if e.get("type") == "blob":
            ns = str(e["path"]).split("/", 1)[0]
            out[ns[: -len(".lean")] if ns.endswith(".lean") else ns] += int(e.get("size", 0))
    return dict(out)


def data_libraries(paths: str) -> tuple[set[str], set[str]]:
    """(the libraries of the tier files, the libraries of data/intake) from `git ls-tree -r --name-only <commit> -- data/trusted data/intake`; a tier library is named as axiom_scan.py names it
    (the stem of data/trusted/<library>.jsonl, or the folder of data/trusted/<library>/<file>.jsonl)"""
    tier: set[str] = set()
    intake: set[str] = set()
    for p in paths.splitlines():
        parts = p.strip().split("/")
        if parts[:2] == ["data", "trusted"] and p.endswith(".jsonl") and len(parts) >= 3:
            tier.add(parts[2][: -len(".jsonl")] if len(parts) == 3 else parts[-2])
        elif parts[:2] == ["data", "intake"] and len(parts) == 4 and parts[3] == "manifest.jsonl":
            intake.add(parts[2])
    return tier, intake


def plan(all_text: str, sizes: dict[str, int], tier: set[str], intake: set[str], shards: int, commit: str | None = None) -> dict:
    roots = all_roots(all_text)
    bad = [r for r in roots if not ROOT.match(r)]
    if "Tengoku" not in roots or bad or len(set(roots)) != len(roots):
        raise SystemExit(
            f"Tengoku/All.lean must import `Tengoku` and each library once (found {len(roots)} imports, bad {bad[:3]}, root present: {'Tengoku' in roots})"
        )
    for lib in tier | intake:
        if not LIBRARY.match(lib):
            raise SystemExit(f"library name {lib!r} is not a plain name")
    by_ns: dict[str, set[str]] = defaultdict(set)
    for lib in tier | intake:
        by_ns[pascal(lib)].add(lib)

    def ns(root: str) -> str:
        return root.split(".", 1)[1]

    libs_roots = [r for r in roots if r != "Tengoku"]
    seed_roots = ["Tengoku"] + [r for r in libs_roots if by_ns.get(ns(r), set()) & tier]
    rest = [r for r in libs_roots if r not in seed_roots]
    weight = {r: sizes.get(ns(r), 0) for r in rest}
    bins: list[dict] = [{"roots": [], "bytes": 0} for _ in range(max(1, shards))]
    for r in sorted(rest, key=lambda r: (-weight[r], r)):  # the largest first, each into the lightest shard
        b = min(bins, key=lambda b: (b["bytes"], len(b["roots"])))
        b["roots"].append(r)
        b["bytes"] += weight[r]
    groups = [
        {
            "shard": 0,
            "roots": seed_roots,
            "libraries": sorted(
                tier
            ),  # every tier library is audited here, once: the compiled ones are in this shard's export, the others are counted by library
            "bytes": sum(sizes.get(ns(r), 0) for r in seed_roots[1:]),
        }
    ]
    for b in sorted((b for b in bins if b["roots"]), key=lambda b: -b["bytes"]):
        roots_here = sorted(b["roots"])
        groups.append(
            {
                "shard": len(groups),
                "roots": roots_here,
                "libraries": sorted(set().union(*(by_ns.get(ns(r), set()) & intake for r in roots_here))),
                "bytes": b["bytes"],
            }
        )
    placed = [r for g in groups for r in g["roots"]]
    if sorted(placed) != sorted(roots):
        raise SystemExit("the shards do not hold exactly the imports of Tengoku/All.lean, each once")
    audited = sorted(x for g in groups for x in g["libraries"])
    if audited != sorted(tier | intake):
        raise SystemExit("a library of data/trusted or data/intake is audited in no shard, or in two")
    return {
        "commit": commit,
        "roots": sorted(roots),
        "shards": groups,
        "roots_without_a_data_library": sorted(r for r in libs_roots if not by_ns.get(ns(r), set())),
    }


def matrix(p: dict) -> dict:
    """the strategy matrix of the workflow: one entry a shard, the roots and the libraries as plain strings (the workflow puts them in the environment, never in a command line)"""
    return {"include": [{"shard": g["shard"], "roots": " ".join(g["roots"]), "libraries": ",".join(g["libraries"])} for g in p["shards"]]}


def merge(p: dict, reports: dict[int, dict], commit: str, lean4export: str, nanoda: str, run: str, now: str | None = None) -> dict:
    """one report from the shards' reports; SystemExit listing every problem when the shards do not make a complete, passing check of `commit`"""
    problems: list[str] = []
    wanted = [g["shard"] for g in p["shards"]]
    if sorted(reports) != sorted(wanted):
        problems.append(f"shards present {sorted(reports)}, expected {sorted(wanted)}")
    toolchains = {r.get("toolchain") for r in reports.values()}
    admitted = {tuple(r.get("nanoda", {}).get("axioms_admitted", [])) for r in reports.values()}
    if len(toolchains) != 1:
        problems.append(f"the shards disagree on the toolchain: {sorted(map(str, toolchains))}")
    if len(admitted) != 1:
        problems.append("the shards admitted different axioms to nanoda")
    for g in p["shards"]:
        r = reports.get(g["shard"])
        if r is None:
            continue
        who = f"shard {g['shard']}"
        for key in ("roots", "libraries"):
            if r.get(key) != g[key]:
                problems.append(f"{who}: its {key} are not the plan's")
        if r.get("commit") != commit:
            problems.append(f"{who}: checked {r.get('commit')}, not {commit}")
        if r.get("lean4export", {}).get("commit") != lean4export or r.get("nanoda", {}).get("commit") != nanoda:
            problems.append(f"{who}: not made by the pinned lean4export and nanoda")
        if r.get("nanoda", {}).get("errors") != 0 or not r.get("nanoda", {}).get("declarations_checked"):
            problems.append(f"{who}: nanoda did not check declarations without errors")
        scan = r.get("axiom_scan", {})
        if scan.get("passed") is not True or scan.get("failures"):
            problems.append(f"{who}: the axiom scan did not pass")
        if scan.get("trusted_records", {}).get("libraries") != g["libraries"]:
            problems.append(f"{who}: the axiom scan audited other libraries than the plan's")
    if problems:
        raise SystemExit("the shards are not a passing independent check of this commit:\n  " + "\n  ".join(problems))
    rs = [reports[i] for i in wanted]
    scans = [r["axiom_scan"] for r in rs]
    resting: dict[str, set[str]] = defaultdict(set)
    for sc in scans:
        for x, users in sc["resting_on_other_axioms"].items():
            resting[x] |= set(users)
    records: dict = {"total": 0, "in_export": 0, "resting_only_on_standard_axioms": 0, "intake_theorems": 0}
    for key in ("resting_on_more", "missing_from_compiled_libraries", "intake_not_under_manifest_name"):
        records[key] = []
    absent: dict[str, int] = defaultdict(int)
    for sc in scans:
        t = sc["trusted_records"]
        for key in ("total", "in_export", "resting_only_on_standard_axioms", "intake_theorems"):
            records[key] += t[key]
        for key in ("resting_on_more", "missing_from_compiled_libraries", "intake_not_under_manifest_name"):
            records[key] += t[key]
        for lib, n in t["not_in_export_libraries_not_compiled"].items():
            absent[lib] += n
    records["not_in_export_libraries_not_compiled"] = dict(sorted(absent.items()))
    first = rs[0]
    return {
        "commit": commit,
        "toolchain": first["toolchain"],
        "checked_at": now or datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "run": run,
        "lean4export": first["lean4export"],
        "nanoda": {
            "repo": first["nanoda"]["repo"],
            "commit": nanoda,
            "declarations_checked": sum(r["nanoda"]["declarations_checked"] for r in rs),
            "errors": 0,
            "axioms_admitted": first["nanoda"]["axioms_admitted"],
        },
        "axiom_scan": {
            "export": {key: sum(sc["export"][key] for sc in scans) for key in ("lines", "terms", "constants")},
            "axioms_declared": sorted({x for sc in scans for x in sc["axioms_declared"]}),
            "standard_axioms": first["axiom_scan"]["standard_axioms"],
            "resting_on_other_axioms": {x: sorted(u) for x, u in sorted(resting.items())},
            "trusted_records": records,
            "failures": [],
            "passed": True,
        },
        "shards": [
            {
                "shard": g["shard"],
                "roots": g["roots"],
                "libraries": g["libraries"],
                "bytes": g["bytes"],
                "declarations_checked": r["nanoda"]["declarations_checked"],
                "export_lines": r["axiom_scan"]["export"]["lines"],
                "export_seconds": r.get("seconds", {}).get("export"),
                "nanoda_seconds": r.get("seconds", {}).get("nanoda"),
            }
            for g, r in zip(p["shards"], rs, strict=True)
        ],
        "note": "Every shard exports the roots it was given and what they import: the seed part of a shard's export is the same constants as another shard's, so `declarations_checked` and the `export` counts are sums over shards, not counts of distinct constants.",
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    pl = sub.add_parser("plan")
    pl.add_argument("--all", required=True, type=Path)
    src = pl.add_mutually_exclusive_group(required=True)
    src.add_argument("--sizes", type=Path, help="the output of `git ls-tree -r -l <commit> -- Tengoku`")
    src.add_argument("--tree-json", type=Path, help="the GitHub API's listing of the Tengoku tree (what the workflow uses)")
    pl.add_argument("--paths", required=True, type=Path)
    pl.add_argument("--shards", type=int, default=6)
    pl.add_argument("--out", required=True, type=Path)
    pl.add_argument("--matrix", required=True, type=Path)
    pl.add_argument("--commit")
    mg = sub.add_parser("merge")
    mg.add_argument("--plan", required=True, type=Path)
    mg.add_argument("--reports", required=True, type=Path)
    mg.add_argument("--commit", required=True)
    mg.add_argument("--lean4export-commit", required=True)
    mg.add_argument("--nanoda-commit", required=True)
    mg.add_argument("--run", required=True)
    mg.add_argument("--out", required=True, type=Path)
    a = ap.parse_args(argv)
    if a.cmd == "plan":
        tier, intake = data_libraries(a.paths.read_text(encoding="utf-8"))
        sizes = (
            sizes_by_namespace(a.sizes.read_text(encoding="utf-8"))
            if a.sizes
            else sizes_from_api(json.loads(a.tree_json.read_text(encoding="utf-8")))
        )
        p = plan(a.all.read_text(encoding="utf-8"), sizes, tier, intake, a.shards, a.commit)
        a.out.write_text(json.dumps(p, indent=1, sort_keys=True) + "\n", encoding="utf-8")
        a.matrix.write_text(json.dumps(matrix(p), separators=(",", ":")) + "\n", encoding="utf-8")
        for g in p["shards"]:
            print(f"shard {g['shard']}: {len(g['roots'])} roots, {len(g['libraries'])} libraries, {g['bytes'] / 1e6:.1f} MB of sources")
        return 0
    p = json.loads(a.plan.read_text(encoding="utf-8"))
    reports: dict[int, dict] = {}
    for f in sorted(a.reports.rglob("shard-*.json")):
        r = json.loads(f.read_text(encoding="utf-8"))
        if r["shard"] in reports:
            raise SystemExit(f"shard {r['shard']} reported twice")
        reports[r["shard"]] = r
    merged = merge(p, reports, a.commit, a.lean4export_commit, a.nanoda_commit, a.run)
    a.out.write_text(json.dumps(merged, indent=2) + "\n", encoding="utf-8")
    print(
        f"independent check of {a.commit}: {len(reports)} shards, {merged['nanoda']['declarations_checked']} declarations checked by nanoda; the counts of records are in {a.out.name}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
