"""tools/correct_statements.py writes the `statement_correction` lines for tentative records the extractor cut too early (tengoku#811, #815, #832).

The real cases:
  * fixtures/real-truncated-tentative-2026-11-13.json.gz (scripts/ci/tests): 543 of the 758 truncated tentative records found on main on 13 Nov 2026, as stored, from 13 libraries;
  * fixtures/real-match-arm-tentative-2026-11-14.json: 10 real records of finite-simple-groups-lean, sandrones-library and tda-lib whose proof starts with a match arm `| ...`. The first version of the helper
    joined statement and proof with a space, which put the first arm on the type's line, and 135 corrections pulled `| 0, y => ...` into the statement (gitar on tengoku#832).

Invariants:
  1. Every correction made for the 543 real truncated records is one the gate accepts: the statement and proof of the line are the old text with the seam moved later (`moves_only` of
     scripts/ci/validate_records.py) and the statement only grows. At least 250 of the records are corrected (263 on 14 Nov 2026).
  2. No correction of a real match-arm record is made, and none of the corrections of invariant 1 has a match arm in its statement.
  3. Mutant: the helper that joins by a space only (the first version) DOES correct real match-arm records, with the arm inside the statement: the test of invariant 2 fails on it.
  4. A second run over the file with its corrections appended makes no line (the newest correction of a name is its current text); a retracted name and a line that is no record are left alone.
  5. The helper takes `moves_only` and the date rule from the validator's source: with that rule made stricter the helper makes fewer lines.
  6. A name that is in data/trusted gets no line (the gate refuses it: its text is the compiled one); the names are found as validate_records.trusted_names finds them, in the real data/trusted.
  7. `--at` that is no date, and a `--reason` that is empty, has a newline or is longer than 300 characters, write nothing and exit with 2 (the gate would reject the lines); a good run exits with 0."""

from __future__ import annotations

import gzip
import importlib.util
import json
import re
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("correct_statements", ROOT / "tools" / "correct_statements.py")
cs = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cs)

TRUNCATED = json.loads(
    gzip.open(ROOT / "scripts/ci/tests/fixtures/real-truncated-tentative-2026-11-13.json.gz", "rt", encoding="utf-8").read()
)["records"]
ARMS = json.loads((ROOT / "scripts/tests/fixtures/real-match-arm-tentative-2026-11-14.json").read_text(encoding="utf-8"))["records"]
ARM_LINE = re.compile(r"(?m)^\s*\|.*=>")
MID_ARM = re.compile(r"[^\n]\s\|\s[^|\n]*=>")


def file_text(records: list[dict]) -> str:
    return "".join(
        json.dumps({"name": r["name"], "statement": r["statement"], "proof": r["proof"]}, ensure_ascii=False) + "\n" for r in records
    )


def by_lib(records: list[dict]) -> dict[str, list[dict]]:
    out: dict[str, list[dict]] = {}
    for r in records:
        out.setdefault(r["lib"], []).append(r)
    return out


class RealTruncated(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lines: list[tuple[dict, dict]] = []
        for lib, recs in by_lib(TRUNCATED).items():
            old = {r["name"]: r for r in recs}
            for c in cs.corrections(file_text(recs), "t", "2026-11-14", "r"):
                cls.lines.append((old[c["statement_correction"]], c))

    def test_enough_records_are_corrected(self):
        self.assertGreaterEqual(len(self.lines), 250)

    def test_every_line_is_one_the_gate_accepts(self):
        for r, c in self.lines:
            self.assertTrue(cs.moves_only(r["statement"], r["proof"], c["statement"], c["proof"]), r["name"])
            self.assertTrue(c["statement"].rstrip().startswith(r["statement"].rstrip()), r["name"])
            self.assertNotEqual((c["statement"], c["proof"]), (r["statement"], r["proof"]))
            self.assertEqual(set(c), {"statement_correction", "statement", "proof", "reason", "by", "at"})

    def test_no_correction_has_a_match_arm_in_its_statement(self):
        for r, c in self.lines:
            self.assertIsNone(ARM_LINE.search(c["statement"]), r["name"])
            self.assertIsNone(MID_ARM.search(c["statement"]), r["name"])


class RealMatchArms(unittest.TestCase):
    def test_the_fixture_is_what_it_says(self):
        self.assertEqual(len(ARMS), 10)
        self.assertEqual({r["lib"] for r in ARMS}, {"finite-simple-groups-lean", "sandrones-library", "tda-lib"})
        for r in ARMS:
            self.assertTrue(r["proof"].lstrip().startswith("|"), r["name"])

    def test_no_arm_record_is_corrected(self):
        self.assertEqual(cs.corrections(file_text(ARMS), "t", "2026-11-14", "r"), [])

    def test_mutant_joining_by_a_space_pulls_the_arm_into_the_statement(self):
        """The first version of the helper: split the text joined by a space only. It makes lines for these real records, and their statements contain the arm."""

        def by_space(name, statement, proof):
            return cs._split(name, statement + " " + proof)

        original = cs.resplit
        cs.resplit = by_space
        try:
            lines = cs.corrections(file_text(ARMS), "t", "2026-11-14", "r")
        finally:
            cs.resplit = original
        self.assertGreaterEqual(len(lines), 5)
        self.assertTrue(any(MID_ARM.search(c["statement"]) for c in lines))


class Behaviour(unittest.TestCase):
    def test_second_run_makes_no_line_and_retracted_names_are_left_alone(self):
        recs = by_lib(TRUNCATED)["nlalib"]
        text = file_text(recs)
        first = cs.corrections(text, "t", "2026-11-14", "r")
        self.assertGreater(len(first), 50)
        appended = text + "".join(json.dumps(c, ensure_ascii=False) + "\n" for c in first)
        self.assertEqual(cs.corrections(appended, "t", "2026-11-14", "r"), [])
        name = first[0]["statement_correction"]
        retracted = text + "not json\n[1, 2]\n" + json.dumps({"tombstone": name}) + "\n"
        again = {c["statement_correction"] for c in cs.corrections(retracted, "t", "2026-11-14", "r")}
        self.assertNotIn(name, again)
        self.assertEqual(len(again), len(first) - 1)

    def test_a_stricter_gate_rule_gives_fewer_lines(self):
        recs = by_lib(TRUNCATED)["abel-formalization"]
        before = len(cs.corrections(file_text(recs), "t", "2026-11-14", "r"))
        original = cs.moves_only
        cs.moves_only = lambda *a: False
        try:
            after = len(cs.corrections(file_text(recs), "t", "2026-11-14", "r"))
        finally:
            cs.moves_only = original
        self.assertGreater(before, 20)
        self.assertEqual(after, 0)


class TrustedAndArguments(unittest.TestCase):
    def test_a_trusted_name_gets_no_line(self):
        recs = by_lib(TRUNCATED)["abel-formalization"]
        lines = cs.corrections(file_text(recs), "t", "2026-11-14", "r")
        self.assertGreater(len(lines), 20)
        name = lines[0]["statement_correction"]
        after = {c["statement_correction"] for c in cs.corrections(file_text(recs), "t", "2026-11-14", "r", {name})}
        self.assertNotIn(name, after)
        self.assertEqual(len(after), len(lines) - 1)

    def test_trusted_names_are_read_from_the_real_data_trusted(self):
        names = cs.trusted_names(ROOT)
        self.assertGreater(len(names), 100_000)
        self.assertEqual(cs.trusted_names(Path(tempfile.mkdtemp())), set())

    def test_arguments_the_gate_would_reject_write_nothing(self):
        recs = by_lib(TRUNCATED)["rankamplificationtotient"]
        good = ["--by", "t", "--at", "2026-11-14", "--reason", "r"]
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "x.jsonl"
            f.write_text(file_text(recs), encoding="utf-8")
            before = f.read_text(encoding="utf-8")
            for bad in (
                ["--by", "t", "--at", "14 Nov", "--reason", "r"],
                ["--by", "t", "--at", "2026-11-14", "--reason", ""],
                ["--by", "t", "--at", "2026-11-14", "--reason", "a\nb"],
                ["--by", "t", "--at", "2026-11-14", "--reason", "x" * 301],
            ):
                self.assertEqual(cs.main([str(f), *bad, "--write"]), 2)
                self.assertEqual(f.read_text(encoding="utf-8"), before)
            self.assertEqual(cs.main([str(f), *good, "--write"]), 0)
            self.assertGreater(len(f.read_text(encoding="utf-8")), len(before))
            self.assertEqual(cs.main([str(f), *good, "--write"]), 0)


if __name__ == "__main__":
    unittest.main()
