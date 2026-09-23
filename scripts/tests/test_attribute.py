"""Bulk attribution: where the credit goes, what is left alone, that a second run changes nothing."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "tools" / "attribute" / "attribute.py"
CREDIT = "Author: Ada Lovelace (https://github.com/ada), with Claude."


def run(d: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(TOOL), str(d), "--credit", CREDIT, *args], capture_output=True, text=True)


def project(files: dict[str, str]) -> Path:
    d = Path(tempfile.mkdtemp())
    for rel, text in files.items():
        p = d / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
    return d


class Attribute(unittest.TestCase):
    def test_bare_declaration_gets_a_docstring_above_its_attributes(self):
        d = project({"A.lean": "open Nat in\n@[simp]\ntheorem foo : 1 = 1 := rfl\n"})
        r = run(d)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((d / "A.lean").read_text(), f"open Nat in\n/-- {CREDIT} -/\n@[simp]\ntheorem foo : 1 = 1 := rfl\n")

    def test_multi_line_attribute_stays_below_the_docstring(self):
        d = project({"A.lean": "@[simp,\n  norm_cast]\nlemma foo : 1 = 1 := rfl\n"})
        run(d)
        self.assertTrue((d / "A.lean").read_text().startswith(f"/-- {CREDIT} -/\n@[simp,\n  norm_cast]\nlemma foo"))

    def test_existing_docstring_gets_the_credit_as_its_last_line(self):
        d = project({"A.lean": "/-- One plus one. -/\ntheorem foo : 1 + 1 = 2 := rfl\n\n/-- Two.\nMore.\n-/\ndef two := 2\n"})
        run(d)
        self.assertEqual(
            (d / "A.lean").read_text(),
            f"/-- One plus one.\n\n{CREDIT} -/\ntheorem foo : 1 + 1 = 2 := rfl\n\n/-- Two.\nMore.\n\n{CREDIT}\n-/\ndef two := 2\n",
        )

    def test_inline_docstring_and_indentation(self):
        d = project({"A.lean": "mutual\n  /-- A. -/ theorem a : 1 = 1 := rfl\n  theorem b : 2 = 2 := rfl\nend\n"})
        run(d)
        self.assertEqual(
            (d / "A.lean").read_text(),
            f"mutual\n  /-- A.\n\n  {CREDIT} -/ theorem a : 1 = 1 := rfl\n  /-- {CREDIT} -/\n  theorem b : 2 = 2 := rfl\nend\n",
        )

    def test_second_run_changes_nothing(self):
        d = project({"A.lean": "/-- Doc. -/\ntheorem foo : 1 = 1 := rfl\ntheorem bar : 2 = 2 := rfl\n"})
        run(d)
        once = (d / "A.lean").read_text()
        r = run(d)
        self.assertEqual((d / "A.lean").read_text(), once)
        self.assertIn("2 already carried this credit", r.stdout)

    def test_another_author_is_left_alone_and_listed(self):
        src = "/-- Theirs.\n\nAuthor: Someone Else. -/\ntheorem foo : 1 = 1 := rfl\n"
        d = project({"A.lean": src})
        r = run(d)
        self.assertEqual((d / "A.lean").read_text(), src)
        self.assertIn("names another author", r.stdout)
        self.assertIn("A.lean:4 foo", r.stdout)

    def test_comments_examples_and_lake_are_untouched(self):
        src = "/- theorem dead : 1 = 1 := rfl -/\n-- theorem gone : 1 = 1 := rfl\nexample : 1 = 1 := rfl\n"
        d = project({"A.lean": src, ".lake/build/B.lean": "theorem cached : 1 = 1 := rfl\n"})
        r = run(d)
        self.assertEqual((d / "A.lean").read_text(), src)
        self.assertEqual((d / ".lake/build/B.lean").read_text(), "theorem cached : 1 = 1 := rfl\n")
        self.assertIn("credited 0 declarations in 1 files", r.stdout)

    def test_dry_run_and_kinds(self):
        src = "theorem foo : 1 = 1 := rfl\ndef two := 2\n"
        d = project({"A.lean": src})
        r = run(d, "--dry-run")
        self.assertEqual((d / "A.lean").read_text(), src)
        self.assertIn("would credit 2 declarations", r.stdout)
        run(d, "--kinds", "theorem")
        self.assertEqual((d / "A.lean").read_text(), f"/-- {CREDIT} -/\ntheorem foo : 1 = 1 := rfl\ndef two := 2\n")

    def test_credit_without_the_marker_is_refused(self):
        d = project({"A.lean": "theorem foo : 1 = 1 := rfl\n"})
        r = subprocess.run([sys.executable, str(TOOL), str(d), "--credit", "Ada Lovelace"], capture_output=True, text=True)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("Author:", r.stderr)
        self.assertEqual((d / "A.lean").read_text(), "theorem foo : 1 = 1 := rfl\n")


if __name__ == "__main__":
    unittest.main()
