"""independent_check.py: the independent check in shards. The planner must put every import of Tengoku/All.lean in exactly one shard and every library of the data in exactly one audit; the merger must
refuse to write the report a release reads unless every shard is there once, for this commit, by the pinned tools, and passed."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))
import independent_check as I  # noqa: E402,N812

ALL = """-- Everything in the tree
import Tengoku.Alpha
import Tengoku.Beta
import Tengoku
import Tengoku.Gamma
import Tengoku.Delta
import Tengoku.EquationalTheories
import Tengoku.MerelyTrue
"""
TIER = {"mathlib-algebra", "mathlib-order", "competemath", "equational-theories"}
INTAKE = {"alpha", "beta", "gamma", "delta"}
SIZES = {"Alpha": 900, "Beta": 500, "Gamma": 450, "Delta": 100, "EquationalTheories": 300, "Seed": 10_000}
L4E, NANODA = "a" * 40, "b" * 40
PATCH = "d" * 64
COMMIT = "c" * 40


def make_plan(shards: int = 2) -> dict:
    return I.plan(ALL, SIZES, TIER, INTAKE, shards, COMMIT)


def shard_report(g: dict, **kw) -> dict:
    r = {
        "shard": g["shard"],
        "roots": g["roots"],
        "libraries": g["libraries"],
        "commit": COMMIT,
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
        "lean4export": {
            "repo": "https://github.com/leanprover/lean4export",
            "commit": L4E,
            **({"patch_sha256": PATCH} if g["shard"] else {}),
        },
        "export_mode": "own" if g["shard"] else "all",
        "nanoda": {
            "repo": "https://github.com/ammkrn/nanoda_lib",
            "commit": NANODA,
            "declarations_checked": 1000 + g["shard"],
            "errors": 0,
            "axioms_admitted": ["propext", "sorryAx"],
        },
        "axiom_scan": {
            "export": {"lines": 100, "terms": 90, "constants": 50},
            "axioms_declared": ["propext", "sorryAx"],
            "standard_axioms": ["Classical.choice", "Quot.sound", "propext"],
            "resting_on_other_axioms": {"sorryAx": []},
            "trusted_records": {
                "total": 10,
                "in_export": 8,
                "resting_only_on_standard_axioms": 8,
                "resting_on_more": [],
                "missing_from_compiled_libraries": [],
                "intake_theorems": 6,
                "intake_not_under_manifest_name": [],
                "not_in_export_libraries_not_compiled": {"mathlib-order": 2} if g["shard"] == 0 else {},
                "libraries": g["libraries"],
            },
            "failures": [],
            "passed": True,
        },
        "seconds": {"export": 100, "nanoda": 20},
    }
    r.update(kw)
    return r


def merge_all(p: dict, mutate=None, **kw):
    reports = {g["shard"]: shard_report(g) for g in p["shards"]}
    if mutate:
        mutate(reports)
    return I.merge(
        p,
        reports,
        kw.get("commit", COMMIT),
        L4E,
        NANODA,
        "https://example/run/1",
        now="2026-11-21T00:00:00Z",
        patch_sha256=kw.get("patch", PATCH),
    )


class Parsing(unittest.TestCase):
    def test_the_imports_of_all_lean_are_the_roots(self):
        self.assertEqual(
            I.all_roots(ALL),
            [
                "Tengoku.Alpha",
                "Tengoku.Beta",
                "Tengoku",
                "Tengoku.Gamma",
                "Tengoku.Delta",
                "Tengoku.EquationalTheories",
                "Tengoku.MerelyTrue",
            ],
        )
        self.assertEqual(I.all_roots("import Lean\nimport Tengoku.Seed.Foo\n-- import Tengoku.X\n"), [])

    def test_sizes_come_from_git_ls_tree(self):
        text = (
            "100644 blob aaaa     120\tTengoku/Alpha.lean\n"
            "100644 blob bbbb     880\tTengoku/Alpha/Sub/A.lean\n"
            "100644 blob cccc      70\tTengoku/Seed/Algebra/X.lean\n"
            "040000 tree dddd       -\tTengoku/Alpha/Sub\n"
            "100644 blob eeee      10\tREADME.md\n"
        )
        self.assertEqual(I.sizes_by_namespace(text), {"Alpha": 1000, "Seed": 70})

    def test_sizes_come_from_the_api_listing_too_and_a_truncated_one_is_refused(self):
        doc = {
            "truncated": False,
            "tree": [
                {"path": "Alpha.lean", "type": "blob", "size": 120},
                {"path": "Alpha/Sub/A.lean", "type": "blob", "size": 880},
                {"path": "Alpha/Sub", "type": "tree"},
                {"path": "Seed/Algebra/X.lean", "type": "blob", "size": 70},
            ],
        }
        self.assertEqual(I.sizes_from_api(doc), {"Alpha": 1000, "Seed": 70})
        with self.assertRaises(SystemExit):
            I.sizes_from_api({**doc, "truncated": True})

    def test_the_libraries_of_the_data_are_named_as_the_axiom_scan_names_them(self):
        paths = "data/trusted/mathlib-algebra.jsonl\ndata/trusted/competemath/pass1.jsonl\ndata/trusted/competemath/pass2.jsonl\ndata/intake/alpha/manifest.jsonl\ndata/intake/alpha/report.json\ndata/intake/alpha/parts/001.json\ndata/stats.json\n"
        self.assertEqual(I.data_libraries(paths), ({"mathlib-algebra", "competemath"}, {"alpha"}))

    def test_a_library_name_becomes_its_module_namespace(self):
        self.assertEqual(
            [I.pascal(x) for x in ("equational-theories", "ben-27-formalization", "jsp000570-lean")],
            ["EquationalTheories", "Ben27Formalization", "Jsp000570Lean"],
        )


class Plan(unittest.TestCase):
    def test_every_root_is_in_exactly_one_shard_and_every_library_is_audited_once(self):
        for shards in (1, 2, 3, 9):
            p = make_plan(shards)
            self.assertEqual(sorted(r for g in p["shards"] for r in g["roots"]), sorted(I.all_roots(ALL)))
            self.assertEqual(sorted(x for g in p["shards"] for x in g["libraries"]), sorted(TIER | INTAKE))

    def test_shard_0_holds_the_seed_the_compiled_tier_libraries_and_all_tier_records(self):
        g = make_plan()["shards"][0]
        self.assertEqual(g["shard"], 0)
        self.assertEqual(g["roots"], ["Tengoku", "Tengoku.EquationalTheories"])
        self.assertEqual(g["libraries"], sorted(TIER))

    def test_the_libraries_that_arrived_as_modules_are_balanced_by_their_sources(self):
        p = make_plan(2)
        sizes = sorted(g["bytes"] for g in p["shards"][1:])
        self.assertEqual(sizes, [950, 1000])  # Alpha 900 + Delta 100, Beta 500 + Gamma 450
        for g in p["shards"][1:]:
            self.assertEqual(g["libraries"], sorted(x for x in INTAKE if f"Tengoku.{I.pascal(x)}" in g["roots"]))

    def test_more_shards_than_libraries_leaves_no_empty_shard(self):
        p = make_plan(50)
        self.assertTrue(all(g["roots"] for g in p["shards"]))
        self.assertEqual(
            len(p["shards"]), 1 + 5
        )  # the seed shard and the five roots that are not tier libraries (four with data, one without)

    def test_a_root_with_no_data_library_is_still_exported_and_is_named(self):
        p = make_plan()
        self.assertEqual(p["roots_without_a_data_library"], ["Tengoku.MerelyTrue"])
        self.assertIn("Tengoku.MerelyTrue", [r for g in p["shards"] for r in g["roots"]])

    def test_the_plan_is_deterministic(self):
        self.assertEqual(json.dumps(make_plan(3), sort_keys=True), json.dumps(make_plan(3), sort_keys=True))

    def test_an_all_lean_without_the_root_or_with_a_repeat_is_refused(self):
        with self.assertRaises(SystemExit):
            I.plan("import Tengoku.Alpha\n", SIZES, TIER, INTAKE, 2)
        with self.assertRaises(SystemExit):
            I.plan(ALL + "import Tengoku.Alpha\n", SIZES, TIER, INTAKE, 2)

    def test_a_library_of_the_data_that_all_lean_does_not_import_is_refused(self):
        with self.assertRaises(SystemExit) as c:
            I.plan(ALL, SIZES, TIER, INTAKE | {"orphan"}, 2)
        self.assertIn("audited in no shard", str(c.exception))

    def test_a_strange_library_name_is_refused_before_it_reaches_a_shell(self):
        with self.assertRaises(SystemExit):
            I.plan(ALL, SIZES, TIER, INTAKE | {"x; rm -rf"}, 2)

    def test_the_matrix_is_plain_strings(self):
        m = I.matrix(make_plan(2))
        self.assertEqual(
            m["include"][0],
            {"shard": 0, "roots": "Tengoku Tengoku.EquationalTheories", "libraries": ",".join(sorted(TIER)), "own": "false"},
        )
        self.assertEqual(
            {e["own"] for e in m["include"][1:]}, {"true"}
        )  # a library shard exports what its libraries declare and what that needs
        self.assertTrue(all(isinstance(v, (str, int)) for e in m["include"] for v in e.values()))


class Merge(unittest.TestCase):
    def test_complete_passing_shards_make_the_report_a_release_reads(self):
        p = make_plan(2)
        r = merge_all(p)
        self.assertEqual((r["commit"], r["axiom_scan"]["passed"], r["axiom_scan"]["failures"]), (COMMIT, True, []))
        self.assertEqual(r["nanoda"]["declarations_checked"], 1000 + 1001 + 1002)
        self.assertEqual(r["nanoda"]["errors"], 0)
        self.assertEqual(r["axiom_scan"]["export"], {"lines": 300, "terms": 270, "constants": 150})
        t = r["axiom_scan"]["trusted_records"]
        self.assertEqual((t["total"], t["in_export"], t["resting_only_on_standard_axioms"], t["intake_theorems"]), (30, 24, 24, 18))
        self.assertEqual(t["not_in_export_libraries_not_compiled"], {"mathlib-order": 2})
        self.assertEqual(r["axiom_scan"]["resting_on_other_axioms"], {"sorryAx": []})
        self.assertEqual([s["shard"] for s in r["shards"]], [0, 1, 2])
        self.assertEqual(r["shards"][1]["export_seconds"], 100)
        self.assertIn("sums over shards", r["note"])
        # the fields release.yml and docs/releases.md read
        for key in ("commit", "toolchain", "checked_at", "run", "lean4export", "nanoda", "axiom_scan"):
            self.assertIn(key, r)

    def test_a_missing_shard_is_refused(self):
        p = make_plan(2)
        with self.assertRaises(SystemExit) as c:
            merge_all(p, lambda reps: reps.pop(2))
        self.assertIn("shards present [0, 1], expected [0, 1, 2]", str(c.exception))

    def test_a_shard_checked_for_another_commit_is_refused(self):
        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), lambda reps: reps[1].update(commit="d" * 40))
        self.assertIn("shard 1: checked", str(c.exception))

    def test_a_shard_made_by_other_tools_is_refused(self):
        def other(reps):
            reps[1]["nanoda"]["commit"] = "e" * 40

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), other)
        self.assertIn("not made by the pinned lean4export and nanoda", str(c.exception))

    def test_a_library_shard_that_did_not_export_its_own_constants_or_ran_another_patch_is_refused(self):
        def wrong_mode(reps):
            reps[1]["export_mode"] = "all"

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), wrong_mode)
        self.assertIn("exported in mode 'all', the plan says 'own'", str(c.exception))

        def seed_in_own_mode(reps):
            reps[0]["export_mode"] = "own"

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), seed_in_own_mode)
        self.assertIn("shard 0: exported in mode 'own', the plan says 'all'", str(c.exception))

        def other_patch(reps):
            reps[2]["lean4export"]["patch_sha256"] = "e" * 64

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), other_patch)
        self.assertIn("shard 2: not made with the patch of this workflow's commit", str(c.exception))
        with self.assertRaises(SystemExit):
            merge_all(make_plan(), patch=None)  # a joiner that is not told the patch cannot vouch for the library shards

    def test_the_merged_report_names_the_patch_the_library_shards_ran_with(self):
        r = merge_all(make_plan())
        self.assertEqual(r["lean4export"]["library_shards_patch_sha256"], PATCH)
        self.assertEqual([s["export_mode"] for s in r["shards"]], ["all", "own", "own"])

    def test_a_failed_scan_or_a_nanoda_error_is_refused(self):
        def scan_failed(reps):
            reps[0]["axiom_scan"]["passed"] = False
            reps[0]["axiom_scan"]["failures"] = ["1 constants rest on sorryAx"]

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), scan_failed)
        self.assertIn("shard 0: the axiom scan did not pass", str(c.exception))

        def nanoda_error(reps):
            reps[2]["nanoda"]["errors"] = 1

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), nanoda_error)
        self.assertIn("shard 2: nanoda did not check", str(c.exception))

    def test_a_shard_with_other_roots_or_libraries_than_the_plans_is_refused(self):
        def swapped(reps):
            reps[1]["roots"], reps[2]["roots"] = reps[2]["roots"], reps[1]["roots"]

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), swapped)
        self.assertIn("its roots are not the plan's", str(c.exception))

        def other_audit(reps):
            reps[1]["axiom_scan"]["trusted_records"]["libraries"] = ["alpha", "beta", "gamma", "delta"]

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), other_audit)
        self.assertIn("audited other libraries", str(c.exception))

    def test_shards_that_disagree_on_the_toolchain_or_the_admitted_axioms_are_refused(self):
        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), lambda reps: reps[1].update(toolchain="leanprover/lean4:v4.35.0"))
        self.assertIn("disagree on the toolchain", str(c.exception))
        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), lambda reps: reps[1]["nanoda"].update(axioms_admitted=["propext"]))
        self.assertIn("admitted different axioms", str(c.exception))

    def test_every_problem_is_listed_not_only_the_first(self):
        def two(reps):
            reps[1]["commit"] = "d" * 40
            reps[2]["nanoda"]["errors"] = 3

        with self.assertRaises(SystemExit) as c:
            merge_all(make_plan(), two)
        self.assertIn("shard 1: checked", str(c.exception))
        self.assertIn("shard 2: nanoda", str(c.exception))

    def test_axioms_that_constants_rest_on_are_joined_across_shards(self):
        def users(reps):
            reps[0]["axiom_scan"]["resting_on_other_axioms"] = {"Lean.trustCompiler": ["Lean.reduceBool"]}
            reps[1]["axiom_scan"]["resting_on_other_axioms"] = {"Lean.trustCompiler": ["Lean.reduceBool", "Lean.reduceNat"]}

        r = merge_all(make_plan(), users)
        self.assertEqual(r["axiom_scan"]["resting_on_other_axioms"]["Lean.trustCompiler"], ["Lean.reduceBool", "Lean.reduceNat"])


class CommandLine(unittest.TestCase):
    def test_plan_then_merge_through_files(self):
        with tempfile.TemporaryDirectory() as d:
            t = Path(d)
            (t / "All.lean").write_text(ALL)
            (t / "ls.txt").write_text("".join(f"100644 blob abc {n}\tTengoku/{ns}.lean\n" for ns, n in SIZES.items()))
            (t / "paths.txt").write_text(
                "".join(f"data/trusted/{x}.jsonl\n" for x in TIER) + "".join(f"data/intake/{x}/manifest.jsonl\n" for x in INTAKE)
            )
            r = subprocess.run(
                [
                    sys.executable,
                    str(CI / "independent_check.py"),
                    "plan",
                    "--all",
                    "All.lean",
                    "--sizes",
                    "ls.txt",
                    "--paths",
                    "paths.txt",
                    "--shards",
                    "2",
                    "--out",
                    "plan.json",
                    "--matrix",
                    "matrix.json",
                    "--commit",
                    COMMIT,
                ],
                cwd=d,
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            plan = json.loads((t / "plan.json").read_text())
            self.assertEqual(plan, make_plan(2))
            matrix = json.loads((t / "matrix.json").read_text())
            self.assertEqual(len(matrix["include"]), 3)
            (t / "reports").mkdir()
            for g in plan["shards"]:
                (t / "reports" / f"shard-{g['shard']}.json").write_text(json.dumps(shard_report(g)))
            r = subprocess.run(
                [
                    sys.executable,
                    str(CI / "independent_check.py"),
                    "merge",
                    "--plan",
                    "plan.json",
                    "--reports",
                    "reports",
                    "--commit",
                    COMMIT,
                    "--lean4export-commit",
                    L4E,
                    "--nanoda-commit",
                    NANODA,
                    "--patch-sha256",
                    PATCH,
                    "--run",
                    "https://example/run/1",
                    "--out",
                    "out.json",
                ],
                cwd=d,
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("3 shards", r.stdout)
            out = json.loads((t / "out.json").read_text())
            self.assertTrue(out["axiom_scan"]["passed"])

    def test_plan_reads_the_api_listing_of_the_tree(self):
        with tempfile.TemporaryDirectory() as d:
            t = Path(d)
            (t / "All.lean").write_text(ALL)
            (t / "tree.json").write_text(
                json.dumps({"truncated": False, "tree": [{"path": f"{ns}.lean", "type": "blob", "size": n} for ns, n in SIZES.items()]})
            )
            (t / "paths.txt").write_text(
                "".join(f"data/trusted/{x}.jsonl\n" for x in TIER) + "".join(f"data/intake/{x}/manifest.jsonl\n" for x in INTAKE)
            )
            r = subprocess.run(
                [
                    sys.executable,
                    str(CI / "independent_check.py"),
                    "plan",
                    "--all",
                    "All.lean",
                    "--tree-json",
                    "tree.json",
                    "--paths",
                    "paths.txt",
                    "--shards",
                    "2",
                    "--out",
                    "plan.json",
                    "--matrix",
                    "matrix.json",
                    "--commit",
                    COMMIT,
                ],
                cwd=d,
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertEqual(json.loads((t / "plan.json").read_text()), make_plan(2))

    def test_merge_writes_nothing_when_a_shard_is_missing(self):
        with tempfile.TemporaryDirectory() as d:
            t = Path(d)
            plan = make_plan(2)
            (t / "plan.json").write_text(json.dumps(plan))
            (t / "reports").mkdir()
            (t / "reports" / "shard-0.json").write_text(json.dumps(shard_report(plan["shards"][0])))
            r = subprocess.run(
                [
                    sys.executable,
                    str(CI / "independent_check.py"),
                    "merge",
                    "--plan",
                    "plan.json",
                    "--reports",
                    "reports",
                    "--commit",
                    COMMIT,
                    "--lean4export-commit",
                    L4E,
                    "--nanoda-commit",
                    NANODA,
                    "--patch-sha256",
                    PATCH,
                    "--run",
                    "x",
                    "--out",
                    "out.json",
                ],
                cwd=d,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(r.returncode, 0)
            self.assertFalse((t / "out.json").exists())

    def test_a_shard_reported_twice_is_refused(self):
        with tempfile.TemporaryDirectory() as d:
            t = Path(d)
            plan = make_plan(2)
            (t / "plan.json").write_text(json.dumps(plan))
            (t / "reports" / "a").mkdir(parents=True)
            (t / "reports" / "b").mkdir(parents=True)
            for sub in ("a", "b"):
                (t / "reports" / sub / "shard-0.json").write_text(json.dumps(shard_report(plan["shards"][0])))
            r = subprocess.run(
                [
                    sys.executable,
                    str(CI / "independent_check.py"),
                    "merge",
                    "--plan",
                    "plan.json",
                    "--reports",
                    "reports",
                    "--commit",
                    COMMIT,
                    "--lean4export-commit",
                    L4E,
                    "--nanoda-commit",
                    NANODA,
                    "--patch-sha256",
                    PATCH,
                    "--run",
                    "x",
                    "--out",
                    "out.json",
                ],
                cwd=d,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("reported twice", r.stdout + r.stderr)


if __name__ == "__main__":
    unittest.main()
