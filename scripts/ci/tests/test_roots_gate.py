"""scripts/ci/roots_gate.py: a group with a root-namespace declaration is reported, and refused once TENGOKU_ROOTS_REQUIRED is 1; so is a report that is not the scanner's whole report."""

import io
import os
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import roots_gate as rg

CLEAN = "leakscan: 0 global instances\nroots: 0 declarations of the library are in the root namespace (x)\n"
DIRTY = "leakscan: 0 global instances\nroots: 3 declarations of the library are in the root namespace (x)\nleak: simp Foo.bar registered in M (declared at line 1)\nroot: X\nroot: C\nroot: X\n"


class RootsGate(unittest.TestCase):
    def test_roots_are_read_once_each_in_order(self):
        self.assertEqual(rg.roots_of(DIRTY), ["X", "C"])
        self.assertEqual(rg.root_lines(DIRTY), ["X", "C", "X"])
        self.assertEqual(rg.roots_of(CLEAN), [])

    def test_a_summary_line_or_a_leak_is_not_a_root(self):
        self.assertEqual(rg.roots_of("roots: 3 declarations\nleak: simp root: X in M\n  root: Y\nrootX\n"), [])

    def test_a_name_with_a_space_in_guillemets_is_a_root(self):
        report = "roots: 2 declarations of the library x\nroot: «foo bar»\nroot: Tengoku.«a b».c\n"
        self.assertEqual(rg.roots_of(report), ["«foo bar»", "Tengoku.«a b».c"])
        self.assertEqual(rg.judge(report, True)[0], 1)

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
        report = "roots: 30 declarations of the library x\n" + "".join(f"root: n{i}\n" for i in range(30))
        code, msg = rg.judge(report, True, shown=5)
        self.assertEqual(code, 1)
        self.assertIn("30 declaration(s)", msg)
        self.assertIn(" …", msg)

    def test_a_scanner_that_crashed_does_not_open_the_gate(self):
        crash = "uncaught exception: unknown package 'Tengoku'\n"
        self.assertEqual(rg.judge("", True)[0], 1)
        self.assertEqual(rg.judge(crash, True)[0], 1)
        self.assertIn("did not finish", rg.judge(crash, True)[1])
        code, msg = rg.judge(crash, False)  # not required: reported, not refused
        self.assertEqual(code, 0)
        self.assertIn("not checked", msg)

    def test_a_cut_report_does_not_open_the_gate(self):
        cut = "roots: 5 declarations of the library x\nroot: A\nroot: B\n"
        code, msg = rg.judge(cut, True)
        self.assertEqual(code, 1)
        self.assertIn("counts 5", msg)
        self.assertEqual(rg.judge(cut, False)[0], 0)

    def run_main(self, report, required):
        env = {k: v for k, v in os.environ.items() if k != "TENGOKU_ROOTS_REQUIRED"}
        if required is not None:
            env["TENGOKU_ROOTS_REQUIRED"] = required
        out = io.StringIO()
        with (
            mock.patch.dict(os.environ, env, clear=True),
            mock.patch.object(sys, "stdin", io.StringIO(report)),
            mock.patch.object(sys, "stdout", out),
        ):
            return rg.main(), out.getvalue()

    def test_main_reads_stdin_and_the_variable(self):
        self.assertEqual(self.run_main(DIRTY, "1")[0], 1)
        self.assertEqual(self.run_main(DIRTY, None)[0], 0)
        self.assertEqual(self.run_main(DIRTY, "0")[0], 0)
        self.assertEqual(self.run_main(CLEAN, "1")[0], 0)
        code, out = self.run_main("", "1")
        self.assertEqual(code, 1)
        self.assertIn("not checked", out)

    def test_a_reported_auto_named_instance_is_exempt_even_when_required(self):
        report = "roots: 2 declarations of the library x\nroot: instAddFoo\nroot: instMulFoo\nroot-instance: instAddFoo\nroot-instance: instMulFoo\n"
        code, msg = rg.judge(report, True)
        self.assertEqual(code, 0)
        self.assertIn("none of the group's declarations", msg)
        self.assertIn("exempt", msg)

    def test_a_real_root_beside_instances_still_fails_and_is_the_one_listed(self):
        report = "roots: 3 declarations of the library x\nroot: instAddFoo\nroot: X\nroot: instMulFoo\nroot-instance: instAddFoo\nroot-instance: instMulFoo\n"
        code, msg = rg.judge(report, True)
        self.assertEqual(code, 1)
        self.assertIn("1 declaration(s)", msg)
        self.assertIn(": X (2 auto-generated", msg)

    def test_a_written_name_that_only_looks_generated_is_a_root(self):
        # a def called instFoo is no instance (the scanner does not report it), an instance called inst_x has no generated shape: both are refused when required
        report = "roots: 2 declarations of the library x\nroot: instFoo\nroot: inst_x\nroot-instance: inst_x\n"
        code, msg = rg.judge(report, True)
        self.assertEqual(code, 1)
        self.assertIn("2 declaration(s)", msg)
        self.assertNotIn("exempt", msg)

    def test_the_shape_of_a_generated_name(self):
        inst = {"instA", "inst_x", "instance", "instantiate", "inst", "Inst", "instFooBar"}
        self.assertEqual({n for n in inst if rg.auto_named(n, inst)}, {"instA", "instFooBar"})
        self.assertFalse(rg.auto_named("instFooBar", set()))  # not reported as an instance


class GeneratedNames(unittest.TestCase):
    """What the final inventory of 2026-11-14 left besides names someone wrote: syntax node kinds (LeanPool `«termℝ²»`, Leanforcontrol `«termD⁺»`: 24) and the generated names of instances
    that are local to their module (Flt `instT2Space`: 23), which the scanner now reports as `root-syntax:` and `root-instance:`."""

    def test_a_syntax_node_kind_is_exempt_even_when_required(self):
        report = "roots: 2 declarations of the library x\nroot: «termℝ²»\nroot: term₃F₂\nroot-syntax: «termℝ²»\nroot-syntax: term₃F₂\n"
        code, msg = rg.judge(report, True)
        self.assertEqual(code, 0)
        self.assertIn("none of the group's declarations", msg)
        self.assertIn("2 generated syntax node kind(s) are exempt: «termℝ²», term₃F₂", msg)

    def test_a_kind_with_a_space_in_its_name_is_read_whole(self):
        report = "roots: 1 declarations of the library x\nroot: «termP(_ ↦ _)»\nroot-syntax: «termP(_ ↦ _)»\n"
        self.assertEqual(rg.syntax_lines(report), {"«termP(_ ↦ _)»"})
        self.assertEqual(rg.judge(report, True)[0], 0)

    def test_a_written_name_beside_generated_ones_still_fails_and_is_the_one_listed(self):
        report = (
            "roots: 4 declarations of the library x\nroot: «termD⁺»\nroot: dim\nroot: instT2Space\nroot: instAddFoo\n"
            "root-instance: instT2Space\nroot-instance: instAddFoo\nroot-syntax: «termD⁺»\n"
        )
        code, msg = rg.judge(report, True)
        self.assertEqual(code, 1)
        self.assertIn("1 declaration(s) of the group are in the root namespace: dim (2 auto-generated instance name(s) are exempt", msg)
        self.assertIn("(1 generated syntax node kind(s) are exempt: «termD⁺»)", msg)

    def test_a_name_that_only_looks_like_a_kind_is_a_root(self):
        # `termFoo` that the scanner does not report as a syntax node kind is a declaration someone wrote
        report = "roots: 2 declarations of the library x\nroot: termFoo\nroot: «termℝ²»\nroot-syntax: «termℝ²»\n"
        code, msg = rg.judge(report, True)
        self.assertEqual(code, 1)
        self.assertIn("1 declaration(s)", msg)
        self.assertIn(": termFoo (1 generated", msg)

    def test_a_syntax_line_for_a_name_that_is_no_root_exempts_nothing(self):
        report = "roots: 1 declarations of the library x\nroot: X\nroot-syntax: Y\n"
        code, msg = rg.judge(report, True)
        self.assertEqual(code, 1)
        self.assertNotIn("exempt", msg)

    def test_a_class_valued_declaration_without_the_generated_shape_is_a_root(self):
        # the scanner reports every declaration of a class as an instance; only the shape Lean generates is exempt
        report = "roots: 2 declarations of the library x\nroot: myMonoid\nroot: instMonoidFoo\nroot-instance: myMonoid\nroot-instance: instMonoidFoo\n"
        code, msg = rg.judge(report, True)
        self.assertEqual(code, 1)
        self.assertIn(": myMonoid (1 auto-generated", msg)

    def test_the_summary_still_counts_every_root_line(self):
        # the extra lines are not `root:` lines: a report cut after them is still caught by the count
        cut = "roots: 3 declarations of the library x\nroot: «termℝ²»\nroot-syntax: «termℝ²»\n"
        self.assertEqual(rg.judge(cut, True)[0], 1)
        self.assertIn("counts 3", rg.judge(cut, True)[1])

    def test_reported_only_until_required(self):
        report = "roots: 2 declarations of the library x\nroot: X\nroot: «termℝ²»\nroot-syntax: «termℝ²»\n"
        code, msg = rg.judge(report, False)
        self.assertEqual(code, 0)
        self.assertIn("reported only", msg)


if __name__ == "__main__":
    unittest.main()
