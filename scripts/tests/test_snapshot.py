"""snapshot.py: the dataset carries what each trusted record states, where it came from, its licence and credit."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def rec(name: str, statement: str, **kw) -> dict:
    return {
        "name": name,
        "statement": statement,
        "proof": ":= rfl",
        "status": "trusted",
        "library": "lib",
        "source_url": "https://github.com/fpvandoorn/Carleson/blob/abc/X.lean",
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
        "promoted_at": "2026-09-01T00:00:00Z",
        **kw,
    }


class Snapshot(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        (self.root / "schemas").mkdir()
        shutil.copy(ROOT / "schemas" / "sources.json", self.root / "schemas" / "sources.json")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n")
        (self.root / "data" / "trusted").mkdir(parents=True)
        (self.root / "data" / "staging" / "lib").mkdir(parents=True)
        doc = "/-- One plus one.\n\nAuthor: Ada Lovelace (https://github.com/ada), with Claude. -/\n"
        lines = [
            rec("Lib.a", doc + "theorem Lib.a : 1 + 1 = 2", headline=True),
            rec("Lib.b", "theorem Lib.b : True"),
            rec("Lib.gone", "theorem Lib.gone : True"),
            {"tombstone": "Lib.gone", "category": "duplicate", "reason": "same as Lib.b", "by": "x", "at": "2026-09-02"},
            {"tombstone_note": "Lib.gone", "note": "see Lib.b", "by": "x", "at": "2026-09-02"},
            {
                "credit_correction": "Lib.b",
                "credit": "Author: Grace Hopper (https://example.org/gh)",
                "evidence": "https://example.org/e",
                "by": "x",
                "at": "2026-09-03",
            },
        ]
        (self.root / "data" / "trusted" / "lib.jsonl").write_text("".join(json.dumps(x) + "\n" for x in lines))
        (self.root / "data" / "staging" / "lib" / "pr-1.jsonl").write_text(
            json.dumps({**rec("Lib.s", "theorem Lib.s : True"), "status": "staging"}) + "\n"
        )

    def tearDown(self):
        shutil.rmtree(self.root)

    def test_dataset_and_manifest(self):
        out = self.root / "out"
        r = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "snapshot.py"), "--out", str(out), "--root", str(self.root)],
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        import gzip

        raw = gzip.decompress((out / "tengoku-dataset.jsonl.gz").read_bytes())
        rows = [json.loads(x) for x in raw.decode().splitlines()]
        by = {x["name"]: x for x in rows}
        self.assertEqual(sorted(by), ["Lib.a", "Lib.b"])  # the retracted record is left out; staging is not in the dataset
        self.assertEqual(by["Lib.a"]["licence"], "Apache-2.0")
        self.assertEqual(by["Lib.a"]["credit"], "Author: Ada Lovelace (https://github.com/ada), with Claude.")
        self.assertTrue(by["Lib.a"]["headline"])
        self.assertEqual(by["Lib.b"]["credit"], "Author: Grace Hopper (https://example.org/gh)")
        self.assertEqual(by["Lib.b"]["credit_corrected_evidence"], "https://example.org/e")
        m = json.loads((out / "snapshot.json").read_text())
        self.assertEqual(m["dataset"]["records"], 2)
        self.assertEqual(m["dataset"]["file"], "tengoku-dataset.jsonl.gz")
        self.assertEqual(m["dataset"]["sha256"], hashlib.sha256((out / "tengoku-dataset.jsonl.gz").read_bytes()).hexdigest())
        self.assertEqual(m["dataset"]["uncompressed_sha256"], hashlib.sha256(raw).hexdigest())
        self.assertEqual(m["libraries"]["lib"], {"trusted": 2, "staging": 1})
        self.assertEqual(m["toolchain"], "leanprover/lean4:v4.34.0-rc2")


if __name__ == "__main__":
    unittest.main()
