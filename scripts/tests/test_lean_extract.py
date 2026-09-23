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


if __name__ == "__main__":
    unittest.main()
