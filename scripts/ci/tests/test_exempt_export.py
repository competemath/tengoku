"""exempt_export.py: nanoda's copy of an export, with the exempt theorems turned into axioms. Nothing else of the export may change, a definition may not be exempt, the list must be well formed,
and the tool says what it applied."""

from __future__ import annotations

import hashlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))
import exempt_export as E  # noqa: E402,N812

REASON = "nanoda does not finish it: its memory grows until the runner is out of it (run 1 of the independent check)"


def entry(name: str, library: str = "lib", reason: str = REASON) -> dict:
    return {"name": name, "library": library, "reason": reason}


def listing(*entries: dict) -> str:
    return json.dumps({"exempt": list(entries)})


# Foo.bar (theorem), Foo.baz (definition), Qux.0.deep (theorem under a numeric component), Foo.other (theorem)
EXPORT = [
    {"meta": {"format": {"version": "3.1.0"}}},
    {"in": 1, "str": {"pre": 0, "str": "Foo"}},
    {"in": 2, "str": {"pre": 1, "str": "bar"}},
    {"in": 3, "str": {"pre": 1, "str": "baz"}},
    {"in": 4, "str": {"pre": 0, "str": "Qux"}},
    {"in": 5, "num": {"i": 0, "pre": 4}},
    {"in": 6, "str": {"pre": 5, "str": "deep"}},
    {"in": 7, "str": {"pre": 1, "str": "other"}},
    {"il": 1, "succ": 0},
    {"ie": 0, "sort": 0},
    {"bvar": 0, "ie": 1},
    {"thm": {"all": [2], "levelParams": [1], "name": 2, "type": 0, "value": 1}},
    {"def": {"all": [3], "hints": "abbrev", "levelParams": [], "name": 3, "safety": "safe", "type": 0, "value": 1}},
    {"thm": {"all": [6], "levelParams": [], "name": 6, "type": 0, "value": 1}},
    {"thm": {"all": [7], "levelParams": [], "name": 7, "type": 0, "value": 1}},
]


def lines(objs) -> list[bytes]:
    return [json.dumps(o, separators=(",", ":"), sort_keys=True).encode() + b"\n" for o in objs]


def run(wanted: set[str], objs=EXPORT) -> tuple[list[bytes], list[str]]:
    src, dst = io.BytesIO(b"".join(lines(objs))), io.BytesIO()
    applied = E.transform(src, dst, wanted)
    return dst.getvalue().splitlines(keepends=True), applied


class Transform(unittest.TestCase):
    def test_a_listed_theorem_becomes_an_axiom_with_its_name_level_parameters_and_type_and_nothing_else_changes(self):
        out, applied = run({"Foo.bar"})
        self.assertEqual(applied, ["Foo.bar"])
        want = lines(EXPORT)
        want[11] = lines([{"axiom": {"isUnsafe": False, "levelParams": [1], "name": 2, "type": 0}}])[0]
        self.assertEqual(out, want)  # the same lines in the same order, one of them replaced

    def test_a_name_under_a_numeric_component_is_found(self):
        _, applied = run({"Qux.0.deep"})
        self.assertEqual(applied, ["Qux.0.deep"])

    def test_several_are_applied_and_listed_sorted(self):
        _, applied = run({"Qux.0.deep", "Foo.other", "Foo.bar"})
        self.assertEqual(applied, ["Foo.bar", "Foo.other", "Qux.0.deep"])

    def test_nothing_is_applied_to_a_name_the_export_does_not_hold(self):
        out, applied = run({"Foo.missing"})
        self.assertEqual((out, applied), (lines(EXPORT), []))

    def test_only_the_whole_name_matches_not_its_last_component(self):
        _, applied = run({"Other.bar"})
        self.assertEqual(applied, [])

    def test_a_definition_cannot_be_exempt(self):
        with self.assertRaises(SystemExit) as cm:
            run({"Foo.baz"})
        self.assertIn("only theorems can be exempt", str(cm.exception))


class Listing(unittest.TestCase):
    def test_a_well_formed_list_is_read(self):
        self.assertEqual(list(E.load_exempt(listing(entry("A.b"), entry("C.d")))), ["A.b", "C.d"])
        self.assertEqual(E.load_exempt(listing()), {})

    def test_an_ill_formed_list_is_refused_with_every_problem(self):
        for text, why in (
            (listing(entry("C.d"), entry("A.b")), "not sorted"),
            (listing(entry("A.b"), entry("A.b")), "listed twice"),
            (listing(entry("A.b", reason="too slow")), "at least 40 characters"),
            (listing({"name": "A.b", "reason": REASON}), "no library"),
            (listing({"library": "x", "reason": REASON}), "without a name"),
            (json.dumps(["A.b"]), '{"exempt"'),
        ):
            with self.subTest(why=why), self.assertRaises(SystemExit) as cm:
                E.load_exempt(text)
            self.assertIn(why, str(cm.exception))


class Repository(unittest.TestCase):
    def test_the_list_the_check_runs_with_is_well_formed(self):
        listed = E.load_exempt((CI / "independent_check_exempt.json").read_text(encoding="utf-8"))
        for name, e in listed.items():
            self.assertRegex(e["library"], r"^[a-z0-9][a-z0-9-]*$", name)  # a key of data/intake, as the plan names libraries


class Occurs(unittest.TestCase):
    def test_the_scan_finds_the_last_component_in_the_name_table(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "export.ndjson"
            f.write_bytes(b"".join(lines(EXPORT)))
            self.assertTrue(E.occurs(f, {"Foo.bar"}))
            self.assertTrue(E.occurs(f, {"X.deep", "Foo.nothere"}))  # one of the last components is there
            self.assertFalse(E.occurs(f, {"Foo.missing"}))


class CommandLine(unittest.TestCase):
    def run_tool(self, d: Path, exempt_text: str):
        (d / "exempt-list.json").write_text(exempt_text)
        (d / "export.ndjson").write_bytes(b"".join(lines(EXPORT)))
        return subprocess.run(
            [sys.executable, str(CI / "exempt_export.py"), "export.ndjson", "nanoda-input.ndjson"], cwd=d, capture_output=True, text=True
        )

    def test_the_copy_is_written_and_the_names_applied_are_reported_with_the_hash_of_the_list(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            text = listing(entry("Foo.bar"), entry("Other.name"))
            r = self.run_tool(d, text)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            applied = json.loads((d / "exempt-applied.json").read_text())
            self.assertEqual(applied, {"file_sha256": hashlib.sha256(text.encode()).hexdigest(), "applied": ["Foo.bar"]})
            self.assertIn(b'{"axiom":', (d / "nanoda-input.ndjson").read_bytes())
            self.assertEqual((d / "export.ndjson").read_bytes(), b"".join(lines(EXPORT)))  # the original is the axiom scan's, untouched

    def test_no_copy_is_written_when_no_listed_theorem_is_in_the_export(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            r = self.run_tool(d, listing(entry("Elsewhere.thm")))
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertEqual(json.loads((d / "exempt-applied.json").read_text())["applied"], [])
            self.assertFalse((d / "nanoda-input.ndjson").exists())

    def test_an_empty_list_applies_nothing(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            r = self.run_tool(d, listing())
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertFalse((d / "nanoda-input.ndjson").exists())

    def test_a_bad_list_stops_the_tool(self):
        with tempfile.TemporaryDirectory() as t:
            r = self.run_tool(Path(t), listing(entry("A.b", reason="no")))
            self.assertNotEqual(r.returncode, 0)

    def test_a_path_outside_the_working_and_temporary_directories_is_refused(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "exempt-list.json").write_text(listing())
            r = subprocess.run(
                [sys.executable, str(CI / "exempt_export.py"), "/etc/passwd", "out.ndjson"], cwd=d, capture_output=True, text=True
            )
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("outside", r.stderr)


if __name__ == "__main__":
    unittest.main()
