#!/usr/bin/env python3
"""independent_check.py - the independent check (.github/workflows/independent-check.yml) in shards. Standard library only.

  independent_check.py plan  --shards N [--commit SHA] [--only SHARD]
  independent_check.py merge --commit SHA --lean4export-commit X --nanoda-commit Y --run URL [--patch-sha256 H] [--nanoda-patch-sha256 H]
  independent_check.py nanoda-config --export FILE

The files it reads and writes are at fixed places under the directory it runs in (the workflow's workspace), not on the command line: plan reads Tengoku/All.lean, tengoku-tree.json (the GitHub API's listing of the
Tengoku tree) and data-paths.txt (the files of data/trusted and data/intake) and writes plan.json and matrix.json; merge reads plan/plan.json, every shard-N.json under shards/ and exempt-list.json (the list of theorems nanoda cannot check, exempt_export.py) and writes independent-check.json; nanoda-config prints the
configuration of nanoda for an export (the axioms it admits: Lean's prelude, and the exempt theorems that shard turned into axioms, from exempt-applied.json).

One `lean4export Tengoku.All` of the whole tree is one process that writes about 13,000 lines a second: 4 h 04 min for 196.6 million lines on 2026-10-12, the last time the check passed. The tree has grown
since, and the job's 350 minutes ran out in the export on every night from 16 November. The tree is cut into SHARDS, each a job of its own:

  shard 0   the seeded root `Tengoku` (all of Lean core and the seed) and the compiled libraries of the tier files (`Tengoku.EquationalTheories`), and the audit of the records of every library of
            `data/trusted` (those whose libraries have no modules in the tree are counted, by library, as before);
  shard 1.. the libraries that arrived as modules (`data/intake`), balanced by the size of their sources; a shard exports the constants declared in the modules of the libraries it was given, and what they
            need (`lean4export --own=<module prefix>`, `scripts/ci/lean4export-own.patch`): a library shard that exported the whole seed it imports as well did not fit in the runner's memory.

Shard 0's `lean4export` of its roots writes every constant of the environment they make (Lean core, the seed, the tier libraries); a library shard writes its own libraries' constants. So the union of the shards holds
every constant `Tengoku.All` has (`plan` checks that the roots of the shards are exactly the imports of `Tengoku/All.lean`, each once). Each shard is checked by nanoda on its own export and by `axiom_scan.py` (every declaration of it for sorryAx and axioms outside the prelude; the records of its own
libraries for the standard three). The libraries of the shards are disjoint, so their record audits add up. `merge` joins the shards' reports into the one report a release reads
(`independent-check.json`: `commit`, `axiom_scan.passed`, ...), and refuses to write it unless every shard is there once, for this commit, by the pinned tools, and passed.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

from exempt_export import APPLIED_JSON, EXEMPT_FILE, load_exempt

# the axioms of Lean's prelude: the export of Lean core declares them (sorryAx, the compiler axioms), nanoda admits them; what the records rest on is audited separately (axiom_scan.py)
NANODA_AXIOMS = ["propext", "Classical.choice", "Quot.sound", "sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"]

IMPORT = re.compile(r"^import (Tengoku(?:\.[A-Za-z0-9_]+)?)\s*$")
ROOT = re.compile(r"^Tengoku(?:\.[A-Za-z0-9_]+)?$")
LIBRARY = re.compile(r"^[A-Za-z0-9._-]+$")


def pascal(s: str) -> str:
    """equational-theories -> EquationalTheories, as scripts/ci/_git.py names a library's modules (and axiom_scan.py does)"""
    return "".join(w[:1].upper() + w[1:] for w in s.replace("_", "-").split("-") if w)


def all_roots(text: str) -> list[str]:
    """the modules Tengoku/All.lean imports: the seeded root `Tengoku` and `Tengoku.<Library>` for every library"""
    return [m.group(1) for ln in text.splitlines() if (m := IMPORT.match(ln))]


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
    """the strategy matrix of the workflow: one entry a shard, the roots and the libraries as plain strings (the workflow puts them in the environment, never in a command line).
    `own` says how the shard exports: shard 0 exports every constant of the environment its roots make (all of Lean core and the seed); a library shard exports the constants DECLARED in its own
    libraries' modules and what they need (`lean4export --own=`, scripts/ci/lean4export-own.patch): the environment it imports holds the whole seed, and exporting all of it in every shard
    outgrew the runner's memory (a shard of the first trial: "the hosted runner lost communication with the server")."""
    return {
        "include": [
            {
                "shard": g["shard"],
                "roots": " ".join(g["roots"]),
                "libraries": ",".join(g["libraries"]),
                "own": "false" if g["shard"] == 0 else "true",
            }
            for g in p["shards"]
        ]
    }


def merge(
    p: dict,
    reports: dict[int, dict],
    commit: str,
    lean4export: str,
    nanoda: str,
    run: str,
    now: str | None = None,
    patch_sha256: str | None = None,
    nanoda_patch_sha256: str | None = None,
    exempt: dict[str, dict] | None = None,
    exempt_sha256: str | None = None,
) -> dict:
    """one report from the shards' reports; SystemExit listing every problem when the shards do not make a complete, passing check of `commit`.
    `exempt` is the list of theorems nanoda cannot check (name -> entry, exempt_export.py): every shard must have run with that list, and the shards together must have applied exactly its names."""
    exempt = exempt or {}
    problems: list[str] = []
    applied: set[str] = set()
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
        want_mode = "all" if g["shard"] == 0 else "own"
        if r.get("export_mode") != want_mode:
            problems.append(f"{who}: exported in mode {r.get('export_mode')!r}, the plan says {want_mode!r}")
        if want_mode == "own" and (not patch_sha256 or r.get("lean4export", {}).get("patch_sha256") != patch_sha256):
            problems.append(f"{who}: not made with the patch of this workflow's commit")
        if r.get("nanoda", {}).get("patch_sha256") != nanoda_patch_sha256:  # None for both: an unpatched checker
            problems.append(f"{who}: nanoda was not built with the patch of this workflow's commit")
        if r.get("nanoda", {}).get("errors") != 0 or not r.get("nanoda", {}).get("declarations_checked"):
            problems.append(f"{who}: nanoda did not check declarations without errors")
        ex = r.get("exempt", {})
        if ex.get("file_sha256") != exempt_sha256:
            problems.append(f"{who}: it ran with another list of exempt theorems than this workflow's commit")
        applied |= set(ex.get("applied", []))
        scan = r.get("axiom_scan", {})
        if scan.get("passed") is not True or scan.get("failures"):
            problems.append(f"{who}: the axiom scan did not pass")
        if scan.get("trusted_records", {}).get("libraries") != g["libraries"]:
            problems.append(f"{who}: the axiom scan audited other libraries than the plan's")
    if sorted(applied - set(exempt)):
        problems.append(f"theorems made axioms for nanoda that the exempt list does not name: {sorted(applied - set(exempt))}")
    if sorted(set(exempt) - applied):
        problems.append(
            f"exempt theorems that no shard applied (the name is stale, or in a library the plan does not export): {sorted(set(exempt) - applied)}"
        )
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
        "lean4export": {**first["lean4export"], **({"library_shards_patch_sha256": patch_sha256} if patch_sha256 else {})},
        "nanoda": {
            "repo": first["nanoda"]["repo"],
            "commit": nanoda,
            **({"patch_sha256": nanoda_patch_sha256} if nanoda_patch_sha256 else {}),
            "declarations_checked": sum(r["nanoda"]["declarations_checked"] for r in rs),
            "errors": 0,
            "axioms_admitted": first["nanoda"]["axioms_admitted"],
            # theorems nanoda took for granted (axioms in its copy of the export): the Lean kernel accepted them and the axiom scan audited them, a second kernel did not re-check them
            "exempt": [{"name": n, "library": e["library"], "reason": e["reason"]} for n, e in sorted(exempt.items())],
            **({"exempt_list_sha256": exempt_sha256} if exempt_sha256 else {}),
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
                "export_mode": r["export_mode"],
                "export_lines": r["axiom_scan"]["export"]["lines"],
                "export_seconds": r.get("seconds", {}).get("export"),
                "nanoda_seconds": r.get("seconds", {}).get("nanoda"),
            }
            for g, r in zip(p["shards"], rs, strict=True)
        ],
        "note": "Shard 0 exports every constant of the environment its roots make (Lean core and the seed); a library shard exports the constants declared in the modules of its own libraries and what they need (lean4export --own): the seed constants a library uses are exported again by its shard, so `declarations_checked` and the `export` counts are sums over shards, not counts of distinct constants. Coverage rests on shard 0 holding the whole seed and on the plan's roots being exactly the imports of Tengoku/All.lean.",
    }


def nanoda_config(export: str, exempt_applied: list[str]) -> dict:
    """the configuration of nanoda for `export`: four checking threads, the Nat and String extensions, and as admitted axioms Lean's prelude and the exempt theorems this export holds as axioms"""
    return {
        "export_file_path": export,
        "use_stdin": False,
        "permitted_axioms": NANODA_AXIOMS + sorted(exempt_applied),
        "unpermitted_axiom_hard_error": True,
        "num_threads": 4,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
        "pp_to_stdout": True,
    }


ALL_LEAN = Path("Tengoku/All.lean")
TREE_JSON = Path("tengoku-tree.json")
DATA_PATHS = Path("data-paths.txt")
PLAN_JSON = Path("plan.json")
MATRIX_JSON = Path("matrix.json")
PLAN_IN = Path("plan") / "plan.json"
SHARDS_DIR = Path("shards")
REPORT_JSON = Path("independent-check.json")


def write(path: Path, text: str) -> None:
    """`open` on one of the fixed paths above and a write of the text: the text comes from command-line arguments and files, the path from nothing but this module (`Path.write_text` made SonarCloud take the text for a path)"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    pl = sub.add_parser("plan")
    pl.add_argument("--shards", type=int, default=24)
    pl.add_argument("--commit")
    pl.add_argument(
        "--only",
        type=int,
        help="run only this shard (a diagnosis of one shard: plan.json still holds all of them, so the run is not a check of the commit and has no report)",
    )
    mg = sub.add_parser("merge")
    mg.add_argument("--commit", required=True)
    mg.add_argument("--lean4export-commit", required=True)
    mg.add_argument("--nanoda-commit", required=True)
    mg.add_argument("--run", required=True)
    mg.add_argument(
        "--nanoda-patch-sha256",
        help="the sha256 of scripts/ci/nanoda.patch at the workflow's commit (the stack size of nanoda's checking threads, and a log of what each one is on): every shard must say it built nanoda with it",
    )
    mg.add_argument(
        "--patch-sha256",
        help="the sha256 of scripts/ci/lean4export-own.patch at the workflow's commit: the library shards must say they ran with it",
    )
    nc = sub.add_parser("nanoda-config")
    nc.add_argument("--export", required=True, help="the export nanoda checks (its path goes into the configuration, it is not read here)")
    a = ap.parse_args(argv)
    if a.cmd == "nanoda-config":
        extra = json.loads(APPLIED_JSON.read_text(encoding="utf-8"))["applied"] if APPLIED_JSON.exists() else []
        print(json.dumps(nanoda_config(a.export, extra), indent=2))
        return 0
    if a.cmd == "plan":
        tier, intake = data_libraries(DATA_PATHS.read_text(encoding="utf-8"))
        sizes = sizes_from_api(json.loads(TREE_JSON.read_text(encoding="utf-8")))
        p = plan(ALL_LEAN.read_text(encoding="utf-8"), sizes, tier, intake, a.shards, a.commit)
        write(PLAN_JSON, json.dumps(p, indent=1, sort_keys=True) + "\n")
        m = matrix(p)
        if a.only is not None:
            m = {"include": [x for x in m["include"] if x["shard"] == a.only]}
            if not m["include"]:
                raise SystemExit(f"the plan has no shard {a.only}")
        write(MATRIX_JSON, json.dumps(m, separators=(",", ":")) + "\n")
        for g in p["shards"]:
            print(f"shard {g['shard']}: {len(g['roots'])} roots, {len(g['libraries'])} libraries, {g['bytes'] / 1e6:.1f} MB of sources")
        return 0
    p = json.loads(PLAN_IN.read_text(encoding="utf-8"))
    reports: dict[int, dict] = {}
    for f in sorted(SHARDS_DIR.rglob("shard-*.json")):
        r = json.loads(f.read_text(encoding="utf-8"))
        if r["shard"] in reports:
            raise SystemExit(f"shard {r['shard']} reported twice")
        reports[r["shard"]] = r
    exempt_text = EXEMPT_FILE.read_text(encoding="utf-8")
    merged = merge(
        p,
        reports,
        a.commit,
        a.lean4export_commit,
        a.nanoda_commit,
        a.run,
        patch_sha256=a.patch_sha256,
        nanoda_patch_sha256=a.nanoda_patch_sha256,
        exempt=load_exempt(exempt_text),
        exempt_sha256=hashlib.sha256(exempt_text.encode("utf-8")).hexdigest(),
    )
    write(REPORT_JSON, json.dumps(merged, indent=2) + "\n")
    print(
        f"independent check of {a.commit}: {len(reports)} shards, {merged['nanoda']['declarations_checked']} declarations checked by nanoda; the counts of records are in {REPORT_JSON.name}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
