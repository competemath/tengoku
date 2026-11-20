"""The harvester keeps a credit docstring with the statement, and nothing else from above it."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("lean_extract", ROOT / "tools" / "lean_extract.py")
lean_extract = importlib.util.module_from_spec(spec)
sys.modules["lean_extract"] = lean_extract  # dataclasses resolve the module through sys.modules
spec.loader.exec_module(lean_extract)


class CreditDocstring(unittest.TestCase):
    def test_credit_docstring_travels_with_the_statement(self):
        src = (
            "/-- One plus one.\n\nAuthor: Ada Lovelace (https://github.com/ada), with Claude. -/\n@[simp]\ntheorem foo : 1 + 1 = 2 := rfl\n"
        )
        (decl,) = lean_extract.extract_declarations(src)
        self.assertEqual(
            decl.statement,
            "/-- One plus one.\n\nAuthor: Ada Lovelace (https://github.com/ada), with Claude. -/\n@[simp]\ntheorem foo : 1 + 1 = 2",
        )
        self.assertEqual(decl.proof, ":= rfl")

    def test_other_docstrings_and_file_headers_stay_behind(self):
        src = "/-\nCopyright (c) 2026.\nAuthors: Someone\n-/\n\n/-- One plus one. -/\ntheorem foo : 1 + 1 = 2 := rfl\n\n/- Authors: in a block comment -/\nlemma bar : 2 = 2 := rfl\n"
        foo, bar = lean_extract.extract_declarations(src)
        self.assertEqual(foo.statement, "theorem foo : 1 + 1 = 2")
        self.assertEqual(bar.statement, "lemma bar : 2 = 2")

    def test_blank_and_comment_lines_between_docstring_and_declaration(self):
        src = "/-- Doc.\n\nAuthor: Ada. -/\n\n-- todo\n@[simp]\ntheorem foo : 1 = 1 := rfl\n"
        (decl,) = lean_extract.extract_declarations(src)
        self.assertTrue(decl.statement.startswith("/-- Doc.\n\nAuthor: Ada. -/"), decl.statement)
        self.assertTrue(decl.statement.endswith("theorem foo : 1 = 1"), decl.statement)

    def test_module_doc_with_authors_is_not_a_credit(self):
        src = "/-! # Section\nAuthors: Someone\n-/\ntheorem foo : 1 = 1 := rfl\n"
        (decl,) = lean_extract.extract_declarations(src)
        self.assertEqual(decl.statement, "theorem foo : 1 = 1")

    def test_every_credited_theorem_keeps_its_own_docstring(self):
        src = "namespace N\n/-- A.\nAuthor: Ada. -/\ntheorem a : 1 = 1 := rfl\n\n/-- B. -/\nlemma b : 2 = 2 := rfl\n\n/-- C.\n\nAuthors: Ada, Bob. -/\nlemma c : 3 = 3 := rfl\nend N\n"
        a, b, c = lean_extract.extract_declarations(src)
        self.assertEqual(a.statement, "/-- A.\nAuthor: Ada. -/\ntheorem a : 1 = 1")
        self.assertEqual(b.statement, "lemma b : 2 = 2")
        self.assertEqual(c.statement, "/-- C.\n\nAuthors: Ada, Bob. -/\nlemma c : 3 = 3")


class Names(unittest.TestCase):
    def test_unicode_names_namespaces_and_comments(self):
        src = (
            "/-! Module doc that says\ntheorem not_a_theorem : True := trivial\n-/\nimport Mathlib\n\n"
            "namespace Zeta23\n/-- Doc. -/\n@[simp]\ntheorem thmA₃ (n : ℕ) : n = n := rfl\n\n"
            "namespace Inner\nlemma «weird name» : 1 = 1 := rfl\nend Inner\n\n"
            "theorem _root_.top : 2 = 2 := rfl\nend Zeta23\n\n"
            "/- theorem commented : 3 = 3 := rfl -/\ntheorem last? : 4 = 4 := rfl\n"
        )
        decls = lean_extract.extract_declarations(src)
        self.assertEqual([d.name for d in decls], ["Zeta23.thmA₃", "Zeta23.Inner.«weird name»", "top", "last?"])
        self.assertEqual([d.line for d in decls], [9, 12, 15, 19])
        self.assertEqual(decls[0].statement, "@[simp]\ntheorem thmA₃ (n : ℕ) : n = n")


class HarvestEndToEnd(unittest.TestCase):
    def test_harvest_keeps_the_credit_in_the_record(self):
        import json
        import os
        import subprocess
        import tempfile

        repo = Path(tempfile.mkdtemp())
        (repo / "Lib").mkdir()
        (repo / "Lib" / "A.lean").write_text(
            "/-- One plus one.\n\nAuthor: Ada Lovelace (https://github.com/ada), with Claude. -/\ntheorem one_one : 1 + 1 = 2 := rfl\n\n/-- Plain. -/\nlemma two : 2 = 2 := rfl\n"
        )
        env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
        for cmd in (["git", "init", "-q"], ["git", "add", "-A"], ["git", "commit", "-q", "-m", "x"]):
            subprocess.run(cmd, cwd=repo, check=True, env=env, capture_output=True)
        out = Path(tempfile.mkdtemp()) / "lib.jsonl"
        r = subprocess.run(
            [
                sys.executable,
                str(ROOT / "tools" / "harvest.py"),
                "--repo",
                str(repo),
                "--library",
                "lib",
                "--toolchain",
                "leanprover/lean4:v4.34.0-rc2",
                "--out",
                str(out),
            ],
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        recs = {json.loads(l)["name"]: json.loads(l) for l in out.read_text().splitlines() if l.strip()}
        self.assertTrue(recs["one_one"]["statement"].startswith("/-- One plus one.\n\nAuthor: Ada Lovelace"), recs["one_one"]["statement"])
        self.assertTrue(recs["one_one"]["statement"].endswith("theorem one_one : 1 + 1 = 2"))
        self.assertEqual(recs["two"]["statement"], "lemma two : 2 = 2")


class AdmitIsSorry(unittest.TestCase):
    """`admit` is Lean's synonym of the `sorry` tactic. Real case: formalizedsparse's Kedlaya.kedlaya_2001a_theorem15 (`:= by   admit`) and kedlaya_2017_theorem13_4
    (`:= by admit`) were harvested as records (batch 13, Gitar on tengoku#930) because only the word `sorry` was refused."""

    def names(self, src: str) -> list[str]:
        return [d.name for d in lean_extract.extract_declarations(src)]

    def test_the_real_admit_proofs_are_refused_and_a_real_proof_is_kept(self):
        src = (
            "namespace Kedlaya\n\n"
            "theorem kedlaya_2001a_theorem15 (x : ℕ) : x = x :=\n  by   admit\n\n"
            "theorem kedlaya_2017_theorem13_4 (x : ℕ) : x + 0 = x := by admit\n\n"
            "theorem proved (x : ℕ) : x + 0 = x := by simp\n\nend Kedlaya\n"
        )
        self.assertEqual(self.names(src), ["Kedlaya.proved"])

    def test_sorry_is_still_refused(self):
        self.assertEqual(self.names("theorem a (x : ℕ) : x = x := by sorry\n\ntheorem b (x : ℕ) : x = x := rfl\n"), ["b"])

    def test_admit_on_its_own_line_in_a_tactic_block_is_refused(self):
        self.assertEqual(self.names("theorem a (x : ℕ) : x = x := by\n  have h : x = x := rfl\n  admit\n"), [])

    def test_a_name_that_only_contains_the_word_is_not_refused(self):
        src = (
            "theorem uses_it (x : ℕ) : x = x := by\n  exact Foo.admit_nonneg x\n\n"
            "theorem other (x : ℕ) : x = x := by\n  exact Bar.admit x\n\n"
            "theorem primed (x : ℕ) : x = x := by\n  exact admit' x\n\n"
            "theorem dotted_primed (x : ℕ) : x = x := by\n  exact h.admit' x\n\n"
            "theorem inner_prime (x : ℕ) : x = x := by\n  exact a'admit x\n"
        )
        self.assertEqual(self.names(src), ["uses_it", "other", "primed", "dotted_primed", "inner_prime"])

    def test_mutant_without_the_admit_check_the_real_proofs_pass(self):
        self.assertFalse(lean_extract._SORRY_RE.search(":= by   admit"))  # the filter as it was lets the admit proof through
        self.assertTrue(lean_extract._contains_sorry(":= by   admit"))


if __name__ == "__main__":
    unittest.main()
