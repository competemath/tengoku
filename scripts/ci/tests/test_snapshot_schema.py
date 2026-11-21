"""scripts/ci/snapshot_schema.py: the schema `snapshot.yml` cuts, `keep` (the previous release's) or `2`, and nothing else."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))
import snapshot_schema as S  # noqa: E402


def cli(d: str, *args: str):
    return subprocess.run([sys.executable, str(CI / "snapshot_schema.py"), *args], cwd=d, capture_output=True, text=True)


class SchemaFor(unittest.TestCase):
    def test_keep_is_the_previous_releases_schema(self):
        self.assertEqual(S.schema_for("keep", {"schema": 1}), 1)
        self.assertEqual(S.schema_for("keep", {"schema": 2}), 2)

    def test_keep_without_a_previous_release_or_a_schema_in_it_is_1(self):
        self.assertEqual(S.schema_for("keep", None), 1)
        self.assertEqual(S.schema_for("keep", {"version": "1.0.0"}), 1)  # releases before the schema field: 1.0.0 is one of them

    def test_2_is_2_whatever_the_previous_release_was(self):
        for previous in (None, {"schema": 1}, {"schema": 2}, {}):
            self.assertEqual(S.schema_for("2", previous), 2)

    def test_anything_else_is_refused(self):
        for choice in ("", "1", "3", "KEEP", "keep ", "2 "):
            with self.assertRaises(SystemExit):
                S.schema_for(choice, {"schema": 1})
        for schema in (0, 3, "2", None):
            with self.assertRaises(SystemExit):
                S.schema_for("keep", {"schema": schema})  # a previous release that names a schema this workflow does not cut


class CommandLine(unittest.TestCase):
    def test_the_previous_manifest_is_read_from_the_working_directory(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(cli(d, "keep").stdout.strip(), "1")  # no previous release
            (Path(d) / "previous").mkdir()
            (Path(d) / "previous" / "snapshot.json").write_text(json.dumps({"schema": 2}))
            self.assertEqual(cli(d, "keep").stdout.strip(), "2")
            self.assertEqual(cli(d, "2").stdout.strip(), "2")
            (Path(d) / "previous" / "snapshot.json").write_text(json.dumps({"version": "1.0.0"}))
            self.assertEqual(cli(d, "keep").stdout.strip(), "1")

    def test_a_wrong_call_fails(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertNotEqual(cli(d).returncode, 0)
            self.assertNotEqual(cli(d, "keep", "2").returncode, 0)
            self.assertNotEqual(cli(d, "3").returncode, 0)


if __name__ == "__main__":
    unittest.main()
