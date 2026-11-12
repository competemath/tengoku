"""scripts/ci/roots_gate.py: a group with a root-namespace declaration is reported, and refused once TENGOKU_ROOTS_REQUIRED is 1."""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import roots_gate as rg  # noqa: E402

CLEAN = "leakscan: 0 global instances\nroots: 0 declarations of the library are in the root namespace (x)\n"
DIRTY = "leakscan: 0 global instances\nroots: 2 declarations of the library are in the root namespace (x)\nleak: simp Foo.bar registered in M (declared at line 1)\nroot: X\nroot: C\nroot: X\n"


class RootsGate(unittest.TestCase):
    def test_roots_are_read_once_each_in_order(self):
        self.assertEqual(rg.roots_of(DIRTY), ["X", "C"])
        self.assertEqual(rg.roots_of(CLEAN), [])

    def test_a_summary_line_or_a_leak_is_not_a_root(self):
        self.assertEqual(rg.roots_of("roots: 3 declarations\nleak: simp root: X in M\n  root: Y\nrootX\n"), [])

    def test_clean_group_passes_either_way(self):
        for required in (False, True):
            self.assertEqual(rg.judge(CLEAN, required)[0], 0)

    def test_dirty_group_is_reported_until_required(self):
        code, msg = rg.judge(DIRTY, False)
        self.assertEqual(code, 0)
        self.assertIn("X, C", msg)
        self.assertIn("reported only", msg)

    def test_dirty_group_fails_when_required(self):
        code, msg = rg.judge(DIRTY, True)
        self.assertEqual(code, 1)
        self.assertIn("error:", msg)
        self.assertIn("--qualify-roots", msg)

    def test_long_list_is_cut(self):
        code, msg = rg.judge("".join(f"root: n{i}\n" for i in range(30)), True, shown=5)
        self.assertEqual(code, 1)
        self.assertIn("30 declaration(s)", msg)
        self.assertIn(" …", msg)


if __name__ == "__main__":
    unittest.main()
