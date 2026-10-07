"""scripts/tawatur.py: the independence test of the tawatur proposal (docs/tawatur.md). Its own file; the tree has no tawatur status."""

from __future__ import annotations

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import tawatur as tw


def proof(name, lib, consts, ident="eq.1h0v.s3.aaaaaaaaaaaa", stmt=()):
    return {
        "id": ident,
        "name": name,
        "lib": lib,
        "closure": [*consts, "propext", "Classical.choice", "Lean.Meta.foo"],
        "statement_closure": list(stmt),
    }


def rows(proofs, **kw):
    return tw.analyse(proofs, **kw)


def run(proofs, *argv):
    d = Path(tempfile.mkdtemp())
    (d / "c.jsonl").write_text("".join(json.dumps(p) + "\n" for p in proofs))
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        rc = tw.main(["report", str(d / "c.jsonl"), *argv])
    return rc, out.getvalue(), err.getvalue()


A = [f"A.c{i}" for i in range(6)]
B = [f"B.c{i}" for i in range(6)]
C = [f"C.c{i}" for i in range(6)]


class Independence(unittest.TestCase):
    def test_three_disjoint_proofs_from_three_libraries_are_tawatur_at_k3(self):
        r = rows([proof("p1", "l1", A), proof("p2", "l2", B), proof("p3", "l3", C)])
        self.assertEqual(len(r), 1)
        self.assertTrue(r[0]["tawatur"])
        self.assertEqual(sorted(r[0]["independent"]), ["p1", "p2", "p3"])

    def test_k_is_a_parameter(self):
        three = [proof("p1", "l1", A), proof("p2", "l2", B), proof("p3", "l3", C)]
        self.assertFalse(rows(three, k=4)[0]["tawatur"])
        self.assertTrue(rows(three[:2], k=2)[0]["tawatur"])

    def test_a_shared_constant_makes_two_proofs_dependent(self):
        r = rows(
            [
                proof("p1", "l1", A),
                proof("p2", "l2", [*B, "A.c0"]),
                proof("p3", "l3", C),
            ]
        )
        self.assertEqual(sorted(r[0]["independent"]), ["p1", "p3"])
        self.assertFalse(r[0]["tawatur"])
        self.assertEqual(r[0]["shared"]["p1 | p2"], 1)

    def test_the_same_library_is_one_chain(self):
        r = rows([proof("p1", "l1", A), proof("p2", "l1", B), proof("p3", "l3", C)])
        self.assertEqual(len(r[0]["independent"]), 2)
        self.assertFalse(r[0]["tawatur"])

    def test_a_proof_without_substance_does_not_count(self):
        r = rows(
            [
                proof("p1", "l1", A),
                proof("p2", "l2", B),
                proof("trivial", "l3", ["T.x"]),
            ]
        )
        self.assertEqual(r[0]["substantial"], ["p1", "p2"])
        self.assertFalse(r[0]["tawatur"])
        self.assertTrue(
            rows(
                [
                    proof("p1", "l1", A),
                    proof("p2", "l2", B),
                    proof("trivial", "l3", ["T.x"]),
                ],
                floor=1,
            )[0]["tawatur"]
        )

    def test_the_forced_layer_is_not_shared_substance(self):
        # every proof reaches propext, Classical.choice and Lean.*: still independent
        r = rows([proof("p1", "l1", A), proof("p2", "l2", B)], k=2)
        self.assertTrue(r[0]["tawatur"])

    def test_the_statements_own_constants_are_ignored(self):
        stmt = ["Nat.Prime", "Nat.gcd"]
        r = rows(
            [
                proof("p1", "l1", [*A, *stmt], stmt=stmt),
                proof("p2", "l2", [*B, *stmt], stmt=stmt),
            ],
            k=2,
        )
        self.assertTrue(r[0]["tawatur"])
        without = rows(
            [proof("p1", "l1", [*A, *stmt]), proof("p2", "l2", [*B, *stmt])], k=2
        )
        self.assertFalse(without[0]["tawatur"])

    def test_what_the_caller_ignores_is_ignored(self):
        shared = ["Mathlib.Foundation.x", "Mathlib.Foundation.y"]
        ps = [proof("p1", "l1", [*A, *shared]), proof("p2", "l2", [*B, *shared])]
        self.assertFalse(rows(ps, k=2)[0]["tawatur"])
        self.assertTrue(
            rows(ps, k=2, prefixes=(*tw.FORCED_PREFIXES, "Mathlib.Foundation."))[0][
                "tawatur"
            ]
        )
        self.assertTrue(rows(ps, k=2, exact=set(shared))[0]["tawatur"])

    def test_the_largest_independent_set_is_found_not_the_first(self):
        # p1 overlaps p2 and p3; p2, p3, p4 are mutually independent
        ps = [
            proof("p1", "l1", [*A, "B.c0", "C.c0"]),
            proof("p2", "l2", B),
            proof("p3", "l3", C),
            proof("p4", "l4", [f"D.c{i}" for i in range(6)]),
        ]
        r = rows(ps, k=3)[0]
        self.assertEqual(sorted(r["independent"]), ["p2", "p3", "p4"])
        self.assertTrue(r["tawatur"])

    def test_different_statements_are_different_groups(self):
        ps = [proof("p1", "l1", A, ident="x"), proof("p2", "l2", B, ident="y")]
        self.assertEqual(rows(ps), [])  # no statement has two proofs

    def test_a_statement_with_one_proof_is_not_a_group(self):
        self.assertEqual(rows([proof("p1", "l1", A)]), [])


class Cli(unittest.TestCase):
    def test_the_report_lists_tawatur_statements_and_counts(self):
        ps = [
            proof("p1", "l1", A),
            proof("p2", "l2", B),
            proof("p3", "l3", C),
            proof("q1", "l1", A, ident="other"),
            proof("q2", "l1", A, ident="other"),
        ]
        rc, out, err = run(ps)
        self.assertEqual(rc, 0)
        self.assertEqual(
            [json.loads(ln)["id"] for ln in out.splitlines()],
            ["eq.1h0v.s3.aaaaaaaaaaaa"],
        )
        self.assertIn(
            "2 statements with two or more proofs; 1 tawatur (k=3, floor=5)", err
        )

    def test_all_shows_every_group_and_the_flags_reach_the_analysis(self):
        ps = [proof("p1", "l1", A), proof("p2", "l2", B)]
        self.assertEqual(json.loads(run(ps, "--all", "--k", "2")[1])["tawatur"], True)
        self.assertEqual(
            json.loads(run(ps, "--all", "--k", "2", "--floor", "7")[1])["tawatur"],
            False,
        )

    def test_an_ignore_file_and_prefix_are_read(self):
        shared = ["Found.x", "Found.y"]
        ps = [proof("p1", "l1", [*A, *shared]), proof("p2", "l2", [*B, *shared])]
        self.assertEqual(run(ps, "--all", "--k", "2")[1].count('"tawatur": true'), 0)
        d = Path(tempfile.mkdtemp())
        (d / "x.txt").write_text("Found.x\nFound.y\n")
        self.assertEqual(
            run(ps, "--all", "--k", "2", "--ignore", str(d / "x.txt"))[1].count(
                '"tawatur": true'
            ),
            1,
        )
        self.assertEqual(
            run(ps, "--all", "--k", "2", "--ignore-prefix", "Found.")[1].count(
                '"tawatur": true'
            ),
            1,
        )


if __name__ == "__main__":
    unittest.main()
