"""axiom_scan.py --libraries: a shard of the independent check audits the records of its own libraries and still scans every declaration of its export.
Without the flag nothing changes (test_axiom_scan_intake.py). A record of a compiled library that is NOT among the shard's libraries is not missing from this export: it is another shard's."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from test_gates import CI, Export  # noqa: E402


def scan(x: Export, records: list[str], manifest: list[str], libraries: str | None):
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "tree.ndjson").write_text("\n".join(x.lines) + "\n")
        (root / "data/trusted").mkdir(parents=True)
        (root / "data/intake/bundle").mkdir(parents=True)
        (root / "Tengoku").mkdir()
        (root / "Tengoku/Lib.lean").write_text("")
        (root / "Tengoku/Bundle.lean").write_text("")
        (root / "data/trusted/lib.jsonl").write_text("".join(json.dumps({"name": r}) + "\n" for r in records))
        (root / "data/intake/bundle/manifest.jsonl").write_text(
            "".join(json.dumps({"name": n, "module": "Tengoku.Bundle.M"}) + "\n" for n in manifest)
        )
        extra = ["--libraries", libraries] if libraries is not None else []
        r = subprocess.run(
            [sys.executable, str(CI / "axiom_scan.py"), "tree.ndjson", "--records", "data/trusted", "--report", "report.json", *extra],
            cwd=d,
            capture_output=True,
            text=True,
        )
        report = json.loads((root / "report.json").read_text()) if (root / "report.json").exists() else None
    return r.returncode, r.stdout + r.stderr, report


def standard() -> Export:
    x = Export()
    for a in ("propext", "Classical.choice", "Quot.sound"):
        x.axiom(a)
    return x


class Libraries(unittest.TestCase):
    def export_with_bundle_only(self) -> Export:
        x = standard()
        p = x.const("propext")
        x.decl("Bundle.good", p, p)
        return x

    def test_the_records_of_another_shards_library_are_not_missing_here(self):
        x = self.export_with_bundle_only()
        code, out, _ = scan(x, ["Lib.elsewhere"], ["Bundle.good"], None)
        self.assertEqual(code, 1, out)  # the whole tree's audit: a compiled library's record the export lacks fails
        code, out, report = scan(x, ["Lib.elsewhere"], ["Bundle.good"], "bundle")
        self.assertEqual(code, 0, out)
        t = report["trusted_records"]
        self.assertEqual((t["total"], t["in_export"], t["intake_theorems"], t["libraries"]), (1, 1, 1, ["bundle"]))

    def test_the_records_of_the_shards_own_library_are_still_audited(self):
        x = self.export_with_bundle_only()
        code, out, _ = scan(x, ["Lib.gone"], ["Bundle.good"], "lib")
        self.assertEqual(code, 1, out)
        self.assertIn("trusted records of compiled libraries are not in the export", out)

    def test_a_name_that_is_a_trusted_record_and_a_manifest_theorem_is_held_to_the_records_rule_in_every_shard(self):
        # `Shared.thm` is a record of the tier library `lib` and a theorem of the bundle's manifest, and the export does not hold it: the whole tree's audit fails it (a record of a compiled library), so does the shard of
        # either library; the shard of the bundle used to excuse it as a bundle theorem renamed in the tree (the record names were taken after the libraries narrowed the records)
        x = self.export_with_bundle_only()
        for libraries in (None, "bundle", "lib"):
            with self.subTest(libraries=libraries):
                code, out, _ = scan(x, ["Shared.thm"], ["Shared.thm", "Bundle.good"], libraries)
                self.assertEqual(code, 1, out)
                self.assertIn("trusted records of compiled libraries are not in the export", out)
        # the control: when the export holds it, no shard fails
        held = self.export_with_bundle_only()
        p = held.const("propext")
        held.decl("Shared.thm", p, p)
        for libraries in (None, "bundle", "lib"):
            with self.subTest(libraries=libraries, held=True):
                code, out, _ = scan(held, ["Shared.thm"], ["Shared.thm", "Bundle.good"], libraries)
                self.assertEqual(code, 0, out)

    def test_every_declaration_of_the_export_is_scanned_whatever_the_libraries_are(self):
        x = standard()
        x.axiom("sorryAx")
        s = x.const("sorryAx")
        x.decl("Other.bad", s, s)  # not a record of any library the shard audits
        code, out, _ = scan(x, [], ["Bundle.good"], "bundle")
        self.assertEqual(code, 1, out)
        self.assertIn("constants rest on sorryAx", out)

    def test_an_empty_list_audits_no_record_and_names_no_library(self):
        x = self.export_with_bundle_only()
        code, out, report = scan(x, ["Lib.gone"], ["Bundle.good"], "")
        self.assertEqual(code, 0, out)
        self.assertEqual(report["trusted_records"]["total"], 0)
        self.assertEqual(report["trusted_records"]["libraries"], [])


if __name__ == "__main__":
    unittest.main()
