"""The queue's regeneration check and a roots PR.

2026-11-13, tengoku#797 (wave 2 of the roots class): ejected by "regenerated derived files differ from the PR" on Tengoku/Toric/Toric/Hopf/GrpAlg.lean (50 deletions). A roots PR edits the
modules of intake libraries in place and touches a manifest only when a record's name starts with a root; Toric has roots but none of its records does, so its manifest was not in the group,
the check regenerated it from its corpus, and the generator, with no records for an intake library, wrote nothing. The libraries of the reports a roots PR adds are skipped now.
Its own file, so that tests of other gates do not conflict with it."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from test_gates import Repo  # noqa: E402

TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"
# stands in for scripts/generate.py: records that the queue ran it
GENERATOR_STUB = "import pathlib, sys\n\nwith pathlib.Path('generated.txt').open('a') as f:\n    f.write(' '.join(sys.argv[1:]) + '\\n')\n"
BASIC = "import Tengoku\n\ntheorem good : 1 + 1 = 2 := rfl\n"
RENAMED = "import Tengoku\n\ntheorem _root_.Tengoku.FxLib.good : 1 + 1 = 2 := rfl\n"
REPORT = "roots: 1 declarations of the library are in the root namespace (x)\nroot: good\n"


class RootsRegenerate(unittest.TestCase):
    def repo(self):
        r = Repo()
        r.write("lean-toolchain", TOOLCHAIN + "\n")
        r.write(
            "schemas/sources.json",
            json.dumps({"corpora": {lib: {"repo": "x", "commit": "c"} for lib in ("fx-lib", "other-lib", "dep-lib")}}),
        )
        r.write("scripts/generate.py", GENERATOR_STUB)
        r.write("Tengoku/FxLib/Fx/Basic.lean", BASIC)
        r.write("Tengoku/FxLib.lean", "import Tengoku.FxLib.Fx.Basic\n")
        r.write(
            "data/intake/fx-lib/manifest.jsonl", json.dumps({"name": "other", "library": "fx-lib"}) + "\n"
        )  # no record starts with the root
        r.write("Tengoku/OtherLib/Basic.lean", "import Tengoku\n\ntheorem o : True := trivial\n")
        r.write(
            "Tengoku/DepLib/Basic.lean", "import Tengoku.FxLib.Fx.Basic\n\ntheorem d : good = good := rfl\n"
        )  # an intake library whose module uses the root name
        r.write("Tengoku/DepLib.lean", "import Tengoku.DepLib.Basic\n")
        r.write("data/intake/dep-lib/manifest.jsonl", json.dumps({"name": "d", "library": "dep-lib"}) + "\n")
        r.commit("three libraries")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def regenerated(self, r):
        for lib in ("fx-lib", "other-lib", "dep-lib"):
            (r.dir / "corpora" / lib / ".git").mkdir(parents=True)  # the corpus is already 'cloned'
        rc, out = r.gate("queue_targets.py", "main", "pr", "--regenerate")
        gen = r.dir / "generated.txt"
        return rc, out, (gen.read_text() if gen.exists() else "")

    def test_a_roots_pr_does_not_regenerate_a_library_whose_manifest_it_does_not_touch(self):
        r = self.repo()
        r.write("data/roots/r-1/FxLib.txt", REPORT)
        r.write("Tengoku/FxLib/Fx/Basic.lean", RENAMED)
        r.commit("roots")
        rc, out, generated = self.regenerated(r)
        self.assertEqual(rc, 0, out)
        self.assertEqual(generated, "", "the generator ran for an intake library a roots PR edited in place")

    def test_a_library_of_the_group_that_has_no_report_is_still_regenerated(self):
        r = self.repo()
        r.write("data/roots/r-1/FxLib.txt", REPORT)
        r.write("Tengoku/FxLib/Fx/Basic.lean", RENAMED)
        r.write("Tengoku/OtherLib/Basic.lean", "import Tengoku\n\ntheorem o : True := by trivial\n")  # a hand edit of another library
        r.commit("roots and a hand edit")
        rc, out, generated = self.regenerated(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("--libraries other-lib", generated)
        self.assertNotIn("--libraries fx-lib", generated)

    def test_without_a_report_the_library_is_regenerated_as_before(self):
        r = self.repo()
        r.write("Tengoku/FxLib/Fx/Basic.lean", RENAMED)
        r.write("Tengoku/FxLib/NOTES.md", "a file that is no module\n")
        r.commit("a group that is no roots PR")
        rc, out, generated = self.regenerated(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("--libraries fx-lib", generated)

    def test_a_module_added_beside_the_report_is_regenerated(self):
        # Gitar on tengoku#821: the group is the diff of every PR in it; only a library changed in place is skipped
        for extra in (
            ("Tengoku/FxLib/Fx/Extra.lean", "import Tengoku\n\ntheorem e : True := trivial\n"),  # a module ADDED
            ("Tengoku/FxLib/NOTES.md", "a file that is no module\n"),
        ):
            r = self.repo()
            r.write("data/roots/r-1/FxLib.txt", REPORT)
            r.write("Tengoku/FxLib/Fx/Basic.lean", RENAMED)
            r.write(*extra)
            r.commit("roots and another change to the same library")
            rc, out, generated = self.regenerated(r)
            self.assertEqual(rc, 0, out)
            self.assertIn("--libraries fx-lib", generated, f"{extra[0]}: the library was not regenerated")

    def test_a_dependent_library_that_a_roots_pr_edits_in_place_is_not_regenerated(self):
        # roots_tree.dependents: the modules of other libraries that use the renamed names open them (62 modules of NavierStokesEuler for LeanPool)
        r = self.repo()
        r.write("data/roots/r-1/FxLib.txt", REPORT)
        r.write("Tengoku/FxLib/Fx/Basic.lean", RENAMED)
        r.write(
            "Tengoku/DepLib/Basic.lean",
            "import Tengoku.FxLib.Fx.Basic\n\nnamespace Tengoku.FxLib end Tengoku.FxLib open Tengoku.FxLib\ntheorem d : good = good := rfl\n",
        )
        r.commit("roots with a dependent")
        rc, out, generated = self.regenerated(r)
        self.assertEqual(rc, 0, out)
        self.assertEqual(generated, "", "the generator ran for a library a roots PR edited in place")

    def test_a_dependent_library_with_a_module_added_is_regenerated(self):
        r = self.repo()
        r.write("data/roots/r-1/FxLib.txt", REPORT)
        r.write("Tengoku/FxLib/Fx/Basic.lean", RENAMED)
        r.write(
            "Tengoku/DepLib/Basic.lean",
            "import Tengoku.FxLib.Fx.Basic\n\nnamespace Tengoku.FxLib end Tengoku.FxLib open Tengoku.FxLib\ntheorem d : good = good := rfl\n",
        )
        r.write("Tengoku/DepLib/Extra.lean", "import Tengoku\n\ntheorem e : True := trivial\n")
        r.commit("roots, a dependent and another change to it")
        rc, out, generated = self.regenerated(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("--libraries dep-lib", generated)


if __name__ == "__main__":
    unittest.main()
