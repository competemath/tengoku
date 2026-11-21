#!/usr/bin/env python3
"""snapshot_schema.py - the schema of the dataset that `snapshot.yml` cuts. Standard library only.

  snapshot_schema.py keep|2

`keep` is the previous release's schema (read from previous/snapshot.json when the workflow has downloaded a previous release, 1 when there is none): what the monthly run does, so a release never changes schema by itself.
`2` cuts a schema 2 dataset (docs/v2.md; 2.0.0 while the previous release is schema 1). Prints the number. An input that is neither, or a previous manifest that names a schema other than 1 or 2, is refused: the workflow
would publish a dataset nobody can read. The previous manifest is read at a fixed place under the directory the script runs in, not from the command line.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

PREVIOUS = Path("previous") / "snapshot.json"
SCHEMAS = (1, 2)


def schema_for(choice: str, previous: dict | None) -> int:
    """`keep` -> the previous manifest's `schema` (1 when it has none or there is no previous release); `2` -> 2"""
    if choice == "2":
        return 2
    if choice != "keep":
        raise SystemExit(f"snapshot_schema: the schema input is `keep` or `2`, not {choice!r}")
    schema = 1 if previous is None else previous.get("schema", 1)
    if schema not in SCHEMAS:
        raise SystemExit(f"snapshot_schema: the previous release names the schema {schema!r}; this workflow cuts {SCHEMAS}")
    return schema


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if len(args) != 1:
        raise SystemExit(__doc__)
    previous = json.loads(PREVIOUS.read_text(encoding="utf-8")) if PREVIOUS.is_file() else None
    print(schema_for(args[0], previous))
    return 0


if __name__ == "__main__":
    sys.exit(main())
