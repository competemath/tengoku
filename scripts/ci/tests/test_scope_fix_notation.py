"""A scope-fix PR for NOTATION (scripts/ci/scope_fix_check.py): a library's global `prefix:80 "-" => complement` is a second reading of every `-(3 * x)` in the tree (lean-pool,
2026-10-17), a global `notation "v" => …` reserves `v` in every file. The PR may make the command `scoped` (in a namespace) or `local` (root namespace) and give the importers the
activation, and nothing else. Scenarios on synthetic repositories, each rule with a case that must fail and one that must pass."""

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_gates as tg  # noqa: E402

CI = tg.CI

BASIC = (
    'import Tengoku\n\nnamespace Fx\nnamespace Mod\n\ndef complement (x : Nat) : Nat := x\n\n/-- the complement -/\nprefix:80 "-" => complement\n\n'
    "lemma l : -1 = 1 := rfl\n\nend Mod\n\nlemma outside : -1 = 1 := rfl\n\nend Fx\n"
)
USE = "import Tengoku\nimport Tengoku.FxLib.Fx.Basic\n\ntheorem use : True := trivial\n"
ROOT = 'import Tengoku\n\nnotation "Gal("K ", "F")" => K ≃ₐ[F] K -- Galois group\n\ntheorem g : True := trivial\n'
NOTE = "-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)\n"
BOT = {"PR_ACTOR": "tengoku-bot", "TENGOKU_BOT": "tengoku-bot"}


class ScopedNotation(unittest.TestCase):
    def repo(self, basic=BASIC, use=USE):
        r = tg.Repo()
        r.write("Tengoku/FxLib/Fx/Basic.lean", basic)
        r.write("Tengoku/FxLib/Fx/Use.lean", use)
        r.write("Tengoku/FxLib.lean", "import Tengoku.FxLib.Fx.Basic\nimport Tengoku.FxLib.Fx.Use\n")
        r.write("data/intake/fx-lib/manifest.jsonl", json.dumps({"name": "Fx.outside", "library": "fx-lib"}) + "\n")
        r.commit("an intake library")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def judge(self, r, basic=None, use=None):
        if basic is not None:
            r.write("Tengoku/FxLib/Fx/Basic.lean", basic)
        if use is not None:
            r.write("Tengoku/FxLib/Fx/Use.lean", use)
        r.commit("scope fix")
        rc, out = r.gate("classify.py", env=BOT)
        if rc != 0:
            return rc, out
        assert "class=scope-fix" in out, out
        return r.gate("scope_fix_check.py")

    SCOPED = BASIC.replace('prefix:80 "-"', 'scoped prefix:80 "-"').replace("end Mod\n", "end Mod\nopen scoped Fx.Mod\n") + NOTE
    USE_OPEN = USE.replace("\ntheorem use", "\nopen scoped Fx.Mod\n\ntheorem use")

    def test_the_exact_transformation_passes(self):
        rc, out = self.judge(self.repo(), self.SCOPED, self.USE_OPEN)
        self.assertEqual(rc, 0, out)
        self.assertIn("scope-fix ok: 2 modules", out)

    def test_an_open_scoped_for_another_namespace_is_refused(self):
        rc, out = self.judge(self.repo(), self.SCOPED, USE.replace("\ntheorem use", "\nopen scoped Real\n\ntheorem use"))
        self.assertNotEqual(rc, 0)
        self.assertIn("`Real` is not a namespace this PR made a `scoped` notation for", out)

    def test_an_open_scoped_without_a_scoped_notation_is_refused(self):
        rc, out = self.judge(self.repo(), None, self.USE_OPEN)
        self.assertNotEqual(rc, 0)
        self.assertIn("is not a namespace this PR made a `scoped` notation for", out)

    def test_scoped_in_the_root_namespace_is_refused(self):
        rc, out = self.judge(self.repo(ROOT), ROOT.replace("notation", "scoped notation", 1))
        self.assertNotEqual(rc, 0)
        self.assertIn("needs a namespace", out)

    def test_a_local_notation_is_declared_again_in_the_importers_and_only_that_text(self):
        local = ROOT.replace("notation", "local notation", 1)
        again = USE.replace("\ntheorem use", '\nlocal notation "Gal("K ", "F")" => K ≃ₐ[F] K\n\ntheorem use')
        rc, out = self.judge(self.repo(ROOT), local, again)
        self.assertEqual(rc, 0, out)
        other = USE.replace("\ntheorem use", '\nlocal notation "Gal("K ", "F")" => K ≃ₐ[G] K\n\ntheorem use')
        rc, out = self.judge(self.repo(ROOT), local, other)
        self.assertNotEqual(rc, 0)
        self.assertIn("an added line must be", out)

    def test_only_a_notation_command_may_gain_the_word(self):
        for basic in (
            BASIC.replace("lemma l", "scoped lemma l"),
            BASIC.replace("def complement", "scoped def complement"),
            BASIC.replace("def complement", "local def complement"),
            BASIC.replace('prefix:80 "-" => complement', 'x prefix:80 "-" => complement').replace(
                "x prefix", "scoped x prefix"
            ),  # not at the start of the command
            BASIC.replace("/-- the complement -/", "/-- the scoped complement -/")
            .replace("scoped", "scoped ", 1)
            .replace("scoped  complement", "scoped complement"),
        ):
            rc, _ = self.judge(self.repo(), basic)
            self.assertNotEqual(rc, 0, basic)

    def test_the_word_must_stand_at_the_start_of_the_command(self):
        base = BASIC.replace('prefix:80 "-"', 'open Fx in prefix:80 "-"')  # the command goes on after something that is not a modifier
        edited = base.replace("in prefix", "in scoped prefix").replace("end Mod\n", "end Mod\nopen scoped Fx.Mod\n") + NOTE
        rc, out = self.judge(self.repo(base), edited, self.USE_OPEN)
        self.assertNotEqual(rc, 0, out)

    def test_the_word_in_a_comment_or_a_string_does_not_count(self):
        rc, _ = self.judge(
            self.repo(), BASIC.replace("-- the complement", "-- scoped the complement").replace("/-- the complement -/", "-- scoped prefix")
        )
        self.assertNotEqual(rc, 0)

    def test_nothing_else_may_change_with_it(self):
        for basic in (
            self.SCOPED.replace("lemma l : -1 = 1", "lemma l : -2 = 2"),
            self.SCOPED.replace("lemma l : -1 = 1 := rfl", "lemma l : -1 = 1 := by rfl"),
            self.SCOPED.replace("\nlemma outside", "\nlemma extra : True := trivial\n\nlemma outside"),
        ):
            rc, _ = self.judge(self.repo(), basic, self.USE_OPEN)
            self.assertNotEqual(rc, 0, basic)

    def test_attributes_and_modifiers_may_stand_before_the_word(self):
        base = BASIC.replace('prefix:80 "-" => complement', '@[inherit_doc complement] private infix : 120 " ∈ " => complement')
        edited = base.replace("private infix", "private scoped infix").replace("end Mod\n", "end Mod\nopen scoped Fx.Mod\n") + NOTE
        rc, out = self.judge(self.repo(base), edited, self.USE_OPEN)
        self.assertEqual(rc, 0, out)

    def test_instances_and_notation_in_one_pr(self):
        base = BASIC.replace("def complement", "instance : Coe Nat Int := ⟨Int.ofNat⟩\n\ndef complement")
        edited = (
            base.replace('prefix:80 "-"', 'scoped prefix:80 "-"')
            .replace("end Mod\n", "end Mod\nopen scoped Fx.Mod\n")
            .replace("instance :", "local instance :")
            + NOTE
        )
        rc, out = self.judge(self.repo(base), edited, self.USE_OPEN)
        self.assertEqual(rc, 0, out)


class Units(unittest.TestCase):
    def setUp(self):
        sys.path.insert(0, str(CI))
        import scope_fix_check

        self.sf = scope_fix_check

    def test_notation_insertion(self):
        f = self.sf.notation_insertion
        self.assertEqual(f('prefix:80 "-" => c', 'scoped prefix:80 "-" => c'), "scoped")
        self.assertEqual(f('notation "v" => 1', 'local notation "v" => 1'), "local")
        self.assertEqual(f('@[inherit_doc X] infix : 120 " ∈ " => f', '@[inherit_doc X] scoped infix : 120 " ∈ " => f'), "scoped")
        self.assertEqual(f('elab "superpose " a:term : term => a', 'scoped elab "superpose " a:term : term => a'), "scoped")
        self.assertEqual(f('macro "Facts " : term => x', 'local macro "Facts " : term => x'), "local")
        self.assertIsNone(f("def x := 1", "scoped def x := 1"))
        self.assertIsNone(f("macro_rules | a => b", "scoped macro_rules | a => b"))  # a rule, not the command
        self.assertIsNone(f('prefix:80 "-" => c', 'prefix:80 "-" => scoped c'))  # not at the command's start
        self.assertIsNone(f("-- prefix x", "-- scoped prefix x"))  # inside a comment
        self.assertIsNone(f('prefix:80 "-" => c', 'prefix:80 "-" => c'))  # nothing inserted
        self.assertIsNone(f('prefix:80 "-" => c', 'scoped prefix:81 "-" => c'))  # something else changed too

    def test_namespace_at(self):
        code = self.sf.mask("namespace A.B\nsection\nnotation x\nend\nend A.B\nnotation y\nnamespace C\nnotation z\n").split("\n")
        self.assertEqual(self.sf.namespace_at(code, 2), "A.B")
        self.assertEqual(self.sf.namespace_at(code, 5), "")
        self.assertEqual(self.sf.namespace_at(code, 7), "C")

    def test_code_end_keeps_a_string_that_holds_dashes(self):
        self.assertEqual(self.sf.code_end('notation "--" => x -- c'), len('notation "--" => x'))
        self.assertEqual(self.sf.code_end('notation "a" => "b\\"--" '), len('notation "a" => "b\\"--"'))

    def test_added_lines_for_notation(self):
        notes = self.sf.Notes()
        notes.ns.add("A.B")
        notes.cmds.add('notation "v" => 1')
        f = self.sf.added_line_errors
        known = {"instance": set(), "simp": set()}
        self.assertEqual(f("p", 1, "open scoped A.B", known, notes), [])
        self.assertTrue(f("p", 1, "open scoped A.B C", known, notes))
        self.assertTrue(f("p", 1, "open scoped A.B", known))  # no notes: nothing was scoped
        self.assertEqual(f("p", 1, 'local notation "v" => 1', known, notes), [])
        self.assertTrue(f("p", 1, 'local notation "v" => 2', known, notes))
        self.assertTrue(f("p", 1, 'notation "v" => 1', known, notes))
        self.assertEqual(
            f(
                "p",
                1,
                "-- Tengoku: 3 notation(s) of this module made scoped or local so they do not change other libraries (generated)",
                known,
                notes,
            ),
            [],
        )


if __name__ == "__main__":
    unittest.main()
