#!/usr/bin/env python3
"""promotion_notify.py <before> <after> <promotion PR> — tell each contributor their theorems are trusted.

A promotion (a commit on main) moves records from data/staging/ to data/trusted/. For every record it made
trusted, this finds the staging file the record left and the pull request that added that file (its squash commit
names it: "... (#N)"), and comments once on each such PR with the names that are now trusted. Records added by the
pipeline's own staging PRs are included: those PRs are the authors' record too. Nothing is changed but comments."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys

from _git import added_lines, changed_files, match, removed_lines, run

MAX_NAMES = 25


def names(lines: list[tuple[int, str]]) -> list[str]:
    out = []
    for _, text in lines:
        if not text.strip():
            continue
        try:
            r = json.loads(text)
        except ValueError:
            continue
        if isinstance(r, dict) and "name" in r and not any(k in r for k in ("tombstone", "tombstone_note", "credit_correction")):
            out.append(str(r["name"]))
    return out


def pr_of(path: str, before: str, name: str) -> str | None:
    """The PR that added `name` to `path`: the oldest commit that added the file (a per-PR file), or the commit that
    added the record's line (the shared flat file)."""
    per_pr = path.count("/") == 3  # data/staging/<library>/<file>.jsonl
    if per_pr:
        subjects = run("log", "--diff-filter=A", "--format=%s", before, "--", path, check=False)
    else:
        subjects = run("log", "--format=%s", "-S", f'"name": "{name}"', before, "--", path, check=False)
        subjects += run("log", "--format=%s", "-S", f'"name":"{name}"', before, "--", path, check=False)
    found = re.findall(r"\(#(\d+)\)\s*$", subjects, re.M)
    return found[-1] if found else None  # oldest first match: git log lists newest first


def main() -> None:
    before, after, promotion = sys.argv[1], sys.argv[2], sys.argv[3]
    trusted: set[str] = set()
    left: dict[str, str] = {}  # name -> the staging file it left
    for _, p in changed_files(before, after):
        if match(p, ["data/trusted/*.jsonl"]):
            trusted.update(names(added_lines(before, after, p)))
        elif match(p, ["data/staging/*.jsonl", "data/staging/*/*.jsonl"]):
            for n in names(removed_lines(before, after, p)):
                left.setdefault(n, p)
    by_pr: dict[str, list[str]] = {}
    unknown = 0
    for n in sorted(trusted):
        path = left.get(n)
        pr = pr_of(path, before, n) if path else None
        if pr and pr != promotion:
            by_pr.setdefault(pr, []).append(n)
        else:
            unknown += 1
    if not by_pr:
        print(f"no contributor PR to tell ({len(trusted)} records promoted, {unknown} without a PR found)")
        return
    for pr, ns in sorted(by_pr.items(), key=lambda kv: int(kv[0])):
        shown = ", ".join(f"`{n}`" for n in ns[:MAX_NAMES]) + (f" and {len(ns) - MAX_NAMES} more" if len(ns) > MAX_NAMES else "")
        body = (
            f"**{len(ns)} of the records this PR added {'is' if len(ns) == 1 else 'are'} now trusted** (promotion #{promotion}): "
            f"{shown}.\n\nTrusted means the whole tree builds with them on the pinned toolchain, with no `sorry` and only the "
            "standard axioms; their source and credit travel with them. Search them at https://competemath.com/tengoku."
        )
        if os.environ.get("TENGOKU_COMMENT_DRY"):
            print(f"would comment on #{pr}:\n{body}\n")
            continue
        r = subprocess.run(["gh", "pr", "comment", pr, "--body", body], check=False, capture_output=True, text=True)
        print(f"#{pr}: {len(ns)} trusted" + ("" if r.returncode == 0 else f" (could not comment: {r.stderr.strip()[:200]})"))
    if unknown:
        print(f"{unknown} promoted records without a PR found (added before per-PR files, or by a direct push)")


if __name__ == "__main__":
    main()
