#!/usr/bin/env python3
"""Promote staging translations into the trusted tree.

A staging record passed both gates as a standalone script. It is TRUSTED
only once its module builds in the tree. For every source file that has
staging records (or just --only <source_path>):

  1. move the file's staging records to data/trusted/<library>.jsonl
     (status "trusted", promoted_at),
  2. regenerate that file's module (scripts/generate.py --only),
  3. `lake build` the module — no errors, no `sorry`;
  4. if that fails: move the records back to staging (with build_error),
     regenerate again so the module reflects only what is trusted (or is
     removed), and report.

Nothing that does not build is ever importable through Tengoku.All.

  python3 scripts/promote.py --corpus <corpus checkout> --library equational-theories [--only <source_path>]

Exit 0 when everything promoted, 2 when some file did not build.
"""
import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate import pascal  # noqa: E402


def load(p: Path) -> list[dict]:
    return [json.loads(l) for l in p.read_text(encoding="utf-8").splitlines() if l.strip()] if p.exists() else []


def dump(p: Path, recs: list[dict]) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in recs), encoding="utf-8")


def module_name(lib_ns: str, corpus_prefix: str, source_path: str) -> str:
    rel = Path(source_path)
    if rel.parts and rel.parts[0] == corpus_prefix:
        rel = Path(*rel.parts[1:])
    return f"Tengoku.{lib_ns}." + ".".join(rel.with_suffix("").parts)


def run(cmd: list[str], cwd: Path, timeout: float) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        return 124, f"timed out after {timeout:.0f}s: {' '.join(cmd)} {(e.stdout or '')[-500:]}"
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, help="checkout of the corpus (dir containing e.g. equational_theories/)")
    ap.add_argument("--library", required=True)
    ap.add_argument("--only", default=None, help="promote just this source_path's records")
    ap.add_argument("--out", default=".")
    args = ap.parse_args()
    out = Path(args.out).resolve()
    lib = args.library
    lib_ns = pascal(lib)
    corpus_prefix = lib.replace("-", "_")
    staging_p = out / "data" / "staging" / f"{lib}.jsonl"
    trusted_p = out / "data" / "trusted" / f"{lib}.jsonl"
    staging = load(staging_p)
    trusted = load(trusted_p)

    groups: dict[str, list[dict]] = {}
    for r in staging:
        if r.get("source_path") and r.get("context") is not None and (not args.only or r["source_path"] == args.only):
            groups.setdefault(r["source_path"], []).append(r)
    if not groups:
        print(f"{lib}: nothing to promote")
        return 0

    gen = [sys.executable, "scripts/generate.py", "--corpus", args.corpus, "--libraries", lib]
    promoted = 0
    failed: list[tuple[str, int, str]] = []
    for sp, recs in sorted(groups.items()):
        now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        moved = []
        for r in recs:
            m = dict(r, status="trusted", promoted_at=now)
            m.pop("build_error", None)
            moved.append(m)
        ids = {id(r) for r in recs}
        staging = [r for r in staging if id(r) not in ids]
        trusted = trusted + moved
        dump(staging_p, staging)
        dump(trusted_p, trusted)

        mod = module_name(lib_ns, corpus_prefix, sp)
        rc, o = run(gen + ["--only", sp], out, 600)
        if rc == 0:
            rc, o = run(["lake", "build", mod], out, 3600)
            if rc == 0 and "declaration uses `sorry`" in o:
                rc, o = 1, "a trusted module may not use sorry\n" + o
        if rc == 0:
            promoted += len(moved)
            print(f"promoted {len(moved)} -> {mod}")
            continue

        err = " ".join(o.split())[-1500:]
        moved_ids = {id(m) for m in moved}
        trusted = [r for r in trusted if id(r) not in moved_ids]
        staging = staging + [dict(r, status="staging", build_error=err[-600:]) for r in recs]
        dump(staging_p, staging)
        dump(trusted_p, trusted)
        run(gen + ["--only", sp], out, 600)  # back to what is trusted for this file (or no module at all)
        failed.append((sp, len(recs), err))
        print(f"NOT promoted ({len(recs)}) {sp}: {err[-500:]}")

    print(f"{lib}: promoted {promoted}; not promoted {sum(n for _, n, _ in failed)} in {len(failed)} file(s)")
    return 0 if not failed else 2


if __name__ == "__main__":
    sys.exit(main())
