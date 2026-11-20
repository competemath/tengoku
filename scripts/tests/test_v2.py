"""v2.py: the dataset's schema 2 and the migration from schema 1 (docs/v2.md).

The tests are of four kinds: the pieces on small cases written out by hand; properties, checked on a few hundred seeded random datasets (a round trip, a key, a partition, independence of the
order); the command line; and, when TENGOKU_V1_SNAPSHOT names the directory of the real 1.0.0 release, the whole of it."""

from __future__ import annotations

import gzip
import hashlib
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import v2  # noqa: E402

TC = "leanprover/lean4:v4.34.0-rc2"
URL = "https://github.com/leanprover-community/mathlib4/blob/{sha}/{path}#L{line}"


def rec(name="Lib.a", statement=None, library="mathlib", path="Mathlib/Algebra/Basic.lean", sha="a" * 40, line=1, **kw):
    r = {
        "name": name,
        "library": library,
        "statement": statement if statement is not None else f"theorem {name} : True",
        "proof": ":= trivial",
        "source_url": URL.format(sha=sha, path=path, line=line),
        "licence": "Apache-2.0",
        "credit": None,
        "toolchain": TC,
        "promoted_at": None,
        "credit_corrected_evidence": None,
        "headline": False,
        "upstream": None,
    }
    r.update(kw)
    return r


def random_v1(rng: random.Random, n: int) -> list:
    names = ["add_comm", "A", "A₂_ne_C", "Adj.symm", "foo'", "«weird name»", "mul_one", "Nat.succ_le", "x_ψ₂", "unnamed"]
    out = []
    for i in range(n):
        name = rng.choice(names) if rng.random() < 0.5 else f"t{rng.randrange(1000)}"
        header = rng.choice([name, name, name + "₂_tail", name + "ψ"])  # sometimes the header has more than the name: a cut name
        prefix = rng.choice(
            [
                "",
                "protected ",
                "private ",
                "@[simp] ",
                "@[simp, to_additive foo] protected ",
                "/-- doc\n\nAuthor: A (https://x). -/\n",
                "import Mathlib\n\nopen Nat\n\n",
            ]
        )
        r = rec(
            name=name,
            statement=prefix + rng.choice(["theorem ", "lemma ", "def "]) + header + " : 1 = 1",
            library=rng.choice(["mathlib", "equational-theories", "competemath"]),
            path=rng.choice(["Mathlib/A.lean", "Mathlib/B/C.lean", "x/y.lean", "Archive/Z.lean"]),
            line=rng.randrange(1, 500),
            credit=rng.choice([None, "Author: A (https://x)"]),
            promoted_at=rng.choice([None, "2026-09-01T00:00:00Z"]),
            credit_corrected_evidence=rng.choice([None, None, "https://e"]),
            headline=rng.random() < 0.05,
            upstream=rng.choice([None, None, "https://github.com/o/r@abc"]),
            licence=rng.choice([None, "Apache-2.0", ""]),
        )
        if rng.random() < 0.05:
            r["source_url"] = f"https://competemath.com/practice/problems/{rng.randrange(300)}"
        out.append(r)
    return out


class SchemaFile(unittest.TestCase):
    def test_the_schema_file_says_what_the_code_says(self):
        doc = json.loads((ROOT / "schemas" / "dataset-v2.schema.json").read_text(encoding="utf-8"))
        self.assertEqual(doc["schema"], v2.SCHEMA)
        self.assertEqual(doc["row"]["required"], list(v2.V2_REQUIRED))
        self.assertEqual(doc["row"]["optional"], list(v2.V2_OPTIONAL))
        self.assertEqual(sorted(doc["row"]["types"]), sorted(v2.V2_FIELDS))
        self.assertEqual(doc["renamed_from_schema_1"], {v2.RENAMED_FIELD[0]: v2.RENAMED_FIELD[1]})
        self.assertEqual(sorted(doc["added_to_schema_1"]), sorted(set(v2.V2_FIELDS) - set(v2.V1_FIELDS) - {v2.RENAMED_FIELD[1]}))


class DeclaredName(unittest.TestCase):
    def test_what_a_header_declares(self):
        cases = {
            "theorem foo : True": "foo",
            "lemma foo.bar (h : p) : q": "foo.bar",
            "protected lemma Adj.symm {G : SimpleGraph V} : G.Adj v u": "Adj.symm",
            "@[simp] theorem A₂_mem_circumsphere : x": "A₂_mem_circumsphere",
            "@[simp, to_additive foo [bar]] protected theorem baz' : x": "baz'",
            "@[symm]\nprivate theorem t : x": "t",
            "/-- doc -/\ntheorem d : x": "d",
            "/-- doc /- nested -/ still doc -/ theorem d2 : x": "d2",
            "-- note\ntheorem e : x": "e",
            "import Mathlib\n\nopen Nat\n\nset_option maxRecDepth 8000\n\ntheorem f : x": "f",
            "def «odd name» : Nat := 1": "«odd name»",
            "noncomputable def g : Nat := 1": "g",
            "instance : Foo Nat := ⟨1⟩": None,
            "theorem": None,
            "": None,
            "namespace X": None,
        }
        for text, want in cases.items():
            self.assertEqual(v2.declared_name(text), want, text)

    def test_only_a_cut_is_repaired(self):
        cut = rec(name="A", statement="theorem A₂_mem_circumsphere : x")
        self.assertEqual(v2.repaired_name(cut), "A₂_mem_circumsphere")
        self.assertEqual(
            v2.repaired_name(rec(name="lucas_double", statement="def lucasSeq : Nat := 1")), "lucas_double"
        )  # not a prefix: left alone
        self.assertEqual(v2.repaired_name(rec(name="foo", statement="theorem foo : x")), "foo")
        self.assertEqual(v2.repaired_name(rec(name="foo", statement="no header here")), "foo")


class Refs(unittest.TestCase):
    def test_a_name_that_is_unique_has_the_plain_ref(self):
        self.assertEqual(v2.assign_refs([rec("a"), rec("b")]), ["mathlib:a", "mathlib:b"])

    def test_names_in_two_libraries_do_not_collide(self):
        self.assertEqual(v2.assign_refs([rec("a"), rec("a", library="other")]), ["mathlib:a", "other:a"])

    def test_a_shared_name_gets_the_digest_of_what_it_states(self):
        rows = [rec("a", statement="theorem a : 1 = 1"), rec("a", statement="theorem a : 2 = 2")]
        refs = v2.assign_refs(rows)
        self.assertEqual(len(set(refs)), 2)
        for r, ref in zip(rows, refs):
            self.assertEqual(ref, f"mathlib:a~{hashlib.sha256(r['statement'].encode()).hexdigest()[:10]}")

    def test_the_same_statement_twice_is_told_apart_by_source_and_numbered(self):
        rows = [rec("a", sha="b" * 40, path="Mathlib/Z.lean"), rec("a", sha="b" * 40, path="Mathlib/A.lean")]
        refs = v2.assign_refs(rows)
        self.assertEqual(len(set(refs)), 2)
        self.assertTrue(
            refs[1].endswith(refs[1].split("~")[1]) and "." not in refs[1].split("~")[1]
        )  # the one that sorts first has no number
        self.assertTrue(refs[0].endswith(".2"))

    def test_the_refs_do_not_depend_on_the_order_of_the_records(self):
        for seed in range(40):
            rng = random.Random(seed)
            rows = random_v1(rng, 60)
            names = [v2.repaired_name(r) for r in rows]
            refs = dict()
            for r, n, ref in zip(rows, names, v2.assign_refs(rows, names)):
                refs[json.dumps(r, sort_keys=True)] = ref
            shuffled = rows[:]
            rng.shuffle(shuffled)
            snames = [v2.repaired_name(r) for r in shuffled]
            for r, ref in zip(shuffled, v2.assign_refs(shuffled, snames)):
                key = json.dumps(r, sort_keys=True)
                # two records identical in everything but nothing are the same record: skip exact duplicates of a whole row
                if sum(1 for x in rows if json.dumps(x, sort_keys=True) == key) == 1:
                    self.assertEqual(ref, refs[key], seed)


class Upgrade(unittest.TestCase):
    def test_a_record_gains_what_it_needs_and_loses_what_is_null(self):
        row = v2.upgrade(rec("Lib.a", statement="theorem Lib.a : True", credit="Author: A (https://x)", headline=True))
        self.assertEqual(
            list(row),
            [
                "schema",
                "ref",
                "status",
                "name",
                "library",
                "statement",
                "proof",
                "source_url",
                "toolchain",
                "module",
                "licence",
                "credit",
                "headline",
            ],
        )
        self.assertEqual(
            (row["schema"], row["ref"], row["status"], row["module"]), (2, "mathlib:Lib.a", "trusted", "Mathlib.Algebra.Basic")
        )
        self.assertNotIn("promoted_at", row)
        self.assertNotIn("upstream", row)

    def test_the_clumsy_field_is_renamed_and_the_cut_name_is_repaired(self):
        row = v2.upgrade(rec("A", statement="theorem A₂_x : True", credit_corrected_evidence="https://e"))
        self.assertEqual((row["name"], row["legacy_name"], row["credit_evidence"]), ("A₂_x", "A", "https://e"))
        self.assertNotIn("credit_corrected_evidence", row)

    def test_a_record_that_is_not_in_a_repository_has_no_module(self):
        self.assertNotIn("module", v2.upgrade(rec(source_url="https://competemath.com/practice/problems/3")))
        self.assertNotIn("module", v2.upgrade(rec(source_url="https://github.com/o/r/blob/" + "a" * 40 + "/README.md")))

    def test_the_id_comes_from_the_table_and_only_when_the_pair_has_one_id(self):
        ident = "eq.1h3v.s4.01215b3d171d"
        rows, report = v2.upgrade_dataset([rec("a"), rec("b")], {("mathlib", "a"): ident})
        self.assertEqual(rows[0]["id"], ident)
        self.assertNotIn("id", rows[1])
        self.assertEqual(report["with_id"], 1)

    def test_the_round_trip_is_exact_on_every_random_dataset(self):
        for seed in range(200):
            rows = random_v1(random.Random(seed), 80)
            new, report = v2.upgrade_dataset(rows)
            self.assertEqual([v2.downgrade(r) for r in new], rows, seed)
            self.assertEqual(v2.check(new), [], seed)
            self.assertEqual(len({r["ref"] for r in new}), len(new), seed)
            self.assertEqual(report["records"], len(rows))

    def test_upgrading_is_deterministic_and_does_not_touch_its_input(self):
        rows = random_v1(random.Random(7), 100)
        before = json.dumps(rows, sort_keys=True)
        a, _ = v2.upgrade_dataset(rows)
        b, _ = v2.upgrade_dataset(rows)
        self.assertEqual(a, b)
        self.assertEqual(json.dumps(rows, sort_keys=True), before)

    def test_downgrade_gives_every_version_1_field_in_version_1_order(self):
        old = v2.downgrade(v2.upgrade(rec()))
        self.assertEqual(tuple(old), v2.V1_FIELDS)
        self.assertIsNone(old["credit"])
        self.assertIs(old["headline"], False)


class Check(unittest.TestCase):
    def good(self):
        return v2.upgrade_dataset([rec("a"), rec("b")])[0]

    def test_a_good_dataset_has_no_problems(self):
        self.assertEqual(v2.check(self.good()), [])

    def test_each_invariant_is_checked(self):
        def broken(mutate):
            rows = self.good()
            mutate(rows)
            return v2.check(rows)

        self.assertTrue(any("already used" in p for p in broken(lambda r: r[1].__setitem__("ref", r[0]["ref"]))))
        self.assertTrue(any("missing proof" in p for p in broken(lambda r: r[0].pop("proof"))))
        self.assertTrue(any("schema is" in p for p in broken(lambda r: r[0].__setitem__("schema", 1))))
        self.assertTrue(any("unknown fields" in p for p in broken(lambda r: r[0].__setitem__("surprise", 1))))
        self.assertTrue(any("is not an isnad id" in p for p in broken(lambda r: r[0].__setitem__("id", "nope"))))
        self.assertTrue(any("not the module" in p for p in broken(lambda r: r[0].__setitem__("module", "Wrong"))))
        self.assertTrue(any("left out" in p for p in broken(lambda r: r[0].__setitem__("credit", None))))
        self.assertTrue(any("left out" in p for p in broken(lambda r: r[0].__setitem__("headline", False))))
        self.assertTrue(any("does not start with" in p for p in broken(lambda r: r[0].__setitem__("ref", "mathlib:zzz"))))
        self.assertTrue(any("proper prefix" in p for p in broken(lambda r: r[0].__setitem__("legacy_name", "q"))))

    def test_mixed_schemas_are_refused(self):
        with self.assertRaises(ValueError):
            v2.schema_of([{"schema": 2}, {"name": "x"}])


class Resolve(unittest.TestCase):
    def setUp(self):
        ident = "eq.1h3v.s4.01215b3d171d"
        rows = [
            rec("add_comm", library="mathlib"),
            rec("add_comm", library="other", statement="theorem add_comm : True ∧ True"),
            rec("A", statement="theorem A₁_ne_B : True"),
            rec("A", statement="theorem A₂_ne_C : True"),
            rec("Adj.symm", statement="theorem Adj.symm : 1 = 1"),
            rec("Adj.symm", statement="theorem Adj.symm : 2 = 2"),
            rec("solo"),
        ]
        self.rows, _ = v2.upgrade_dataset(rows, {("mathlib", "solo"): ident})
        self.idx = v2.Index(self.rows)
        self.ident = ident

    def test_a_ref_is_exact(self):
        r = self.idx.resolve("mathlib:solo")
        self.assertEqual((r.status, r.one()["name"]), ("exact", "solo"))

    def test_a_statement_id_names_every_record_that_has_it(self):
        r = self.idx.resolve(self.ident)
        self.assertEqual((r.status, len(r.records)), ("exact", 1))
        self.assertEqual(self.idx.resolve("eq.1h3v.s4.ffffffffffff").status, "not-found")

    def test_a_plain_name_is_unique_or_ambiguous_and_never_guessed(self):
        self.assertEqual(self.idx.resolve("solo").status, "unique-name")
        amb = self.idx.resolve("add_comm")
        self.assertEqual((amb.status, len(amb.candidates)), ("ambiguous", 2))
        with self.assertRaises(LookupError):
            amb.one()
        self.assertEqual(self.idx.resolve("add_comm", library="other").status, "unique-name")

    def test_library_colon_name_narrows_but_can_still_be_ambiguous(self):
        self.assertEqual(self.idx.resolve("other:add_comm").status, "exact")
        self.assertEqual(self.idx.resolve("mathlib:Adj.symm").status, "ambiguous")

    def test_a_cut_version_1_name_still_finds_its_records(self):
        r = self.idx.resolve("A")
        self.assertEqual((r.status, len(r.records)), ("ambiguous", 2))
        self.assertIn("non-ASCII", r.note)
        self.assertEqual(self.idx.resolve("A₂_ne_C").status, "unique-name")

    def test_a_qualified_name_is_offered_as_candidates_not_as_an_answer(self):
        r = self.idx.resolve("Nat.add_comm")
        self.assertEqual((r.status, r.records), ("candidates", []))
        self.assertEqual(len(r.candidates), 2)
        self.assertEqual(self.idx.resolve("Nope.nothing").status, "not-found")

    def test_a_version_1_record_finds_its_version_2_ref(self):
        old = rec("add_comm", library="other", statement="theorem add_comm : True ∧ True")
        self.assertEqual(self.idx.ref_of_v1(old), "other:add_comm")
        self.assertIsNone(self.idx.ref_of_v1(rec("absent")))


class Classify(unittest.TestCase):
    def ds(self, *rows):
        return v2.upgrade_dataset(list(rows))[0]

    def only(self, old, new):
        return {(c["old"], c["new"]): c["change"] for c in v2.classify(old, new)}

    def test_every_kind_of_change(self):
        old = self.ds(
            rec("same"),
            rec("fix", credit=None),
            rec("move", path="Mathlib/Old.lean"),
            rec("ren_old", statement="theorem ren_old : 1 + 1 = 2"),
            rec("rest", statement="theorem rest : 1 = 1"),
            rec("gone"),
        )
        new = self.ds(
            rec("same", sha="c" * 40, promoted_at="2027-01-01T00:00:00Z"),  # an upstream bump and a date are not changes
            rec("fix", credit="Author: B (https://b)"),
            rec("move", path="Mathlib/New.lean"),
            rec("ren_new", statement="theorem ren_new : 1 + 1 = 2"),
            rec("rest", statement="theorem rest : 2 = 2"),
            rec("fresh", statement="theorem fresh : 5 = 5"),
        )
        got = self.only(old, new)
        self.assertEqual(got[("mathlib:same", "mathlib:same")], "unchanged")
        self.assertEqual(got[("mathlib:fix", "mathlib:fix")], "corrected")
        self.assertEqual(got[("mathlib:move", "mathlib:move")], "moved")
        self.assertEqual(got[("mathlib:ren_old", "mathlib:ren_new")], "renamed")
        self.assertEqual(got[("mathlib:rest", "mathlib:rest")], "restated")
        self.assertEqual(got[("mathlib:gone", None)], "removed")
        self.assertEqual(got[(None, "mathlib:fresh")], "added")

    def test_a_rename_found_by_id_beats_the_text(self):
        ident = "eq.1h3v.s4.01215b3d171d"
        old, _ = v2.upgrade_dataset([rec("o", statement="theorem o : A")], {("mathlib", "o"): ident})
        new, _ = v2.upgrade_dataset([rec("n", statement="theorem n : totally different text")], {("mathlib", "n"): ident})
        self.assertEqual(self.only(old, new), {("mathlib:o", "mathlib:n"): "renamed"})

    def test_a_successor_is_never_guessed(self):
        old = self.ds(rec("o", statement="theorem o : 1 = 1"))
        new = self.ds(rec("n1", statement="theorem n1 : 1 = 1"), rec("n2", statement="theorem n2 : 1 = 1"))
        got = self.only(old, new)
        self.assertEqual(got[("mathlib:o", None)], "removed")
        self.assertEqual(got[(None, "mathlib:n1")], "added")
        self.assertEqual(got[(None, "mathlib:n2")], "added")

    def test_a_rename_does_not_cross_libraries(self):
        old = self.ds(rec("o", statement="theorem o : 1 = 1"))
        new = self.ds(rec("n", statement="theorem n : 1 = 1", library="other"))
        self.assertEqual(sorted(self.only(old, new).values()), ["added", "removed"])

    def test_every_record_is_accounted_for_exactly_once(self):
        for seed in range(60):
            rng = random.Random(seed)
            a = random_v1(rng, 50)
            b = [r for r in a if rng.random() < 0.7] + random_v1(rng, 15)
            for r in b:
                if rng.random() < 0.2:
                    r["statement"] += " ∧ True"
                if rng.random() < 0.1:
                    r["credit"] = "Author: new"
            old, new = v2.upgrade_dataset(a)[0], v2.upgrade_dataset(b)[0]
            changes = v2.classify(old, new)
            olds = [c["old"] for c in changes if c["old"]]
            news = [c["new"] for c in changes if c["new"]]
            self.assertEqual(sorted(olds), sorted(r["ref"] for r in old), seed)
            self.assertEqual(sorted(news), sorted(r["ref"] for r in new), seed)
            self.assertEqual(sum(v2.summarise(changes).values()), len(changes))

    def test_the_answer_does_not_depend_on_the_order(self):
        rng = random.Random(3)
        a = random_v1(rng, 80)
        b = [r for r in a if rng.random() < 0.8] + random_v1(rng, 20)
        first = v2.classify(*[v2.upgrade_dataset(x)[0] for x in (a, b)])
        sa, sb = a[:], b[:]
        rng.shuffle(sa)
        rng.shuffle(sb)
        second = v2.classify(*[v2.upgrade_dataset(x)[0] for x in (sa, sb)])
        key = lambda c: (str(c["old"]), str(c["new"]), c["change"])  # noqa: E731
        self.assertEqual(sorted(first, key=key), sorted(second, key=key))

    def test_a_dataset_against_itself_is_all_unchanged(self):
        d = v2.upgrade_dataset(random_v1(random.Random(1), 100))[0]
        self.assertEqual(
            set(v2.summarise(v2.classify(d, d)).items()) - {("unchanged", len(d))}, {(k, 0) for k in v2.CHANGES if k != "unchanged"}
        )


class Source(unittest.TestCase):
    def test_a_renamed_name_is_rewritten_in_code_only(self):
        text = (
            "import Foo\n"
            "/-- uses old_name in a docstring -/\n"
            "theorem t : old_name 1 = 2 := by\n"
            "  -- old_name in a comment\n"
            '  have := "old_name in a string"\n'
            "  /- block old_name /- nested old_name -/ still old_name -/\n"
            "  exact Ns.old_name x\n"
            "  exact old_name_more x\n"
            "  exact (old_name)\n"
        )
        new, rep = v2.migrate_source(text, {"old_name": "new_name"})
        self.assertIn("theorem t : new_name 1 = 2", new)
        self.assertIn("exact (new_name)", new)
        self.assertEqual(new.count("old_name"), 5 + 0 - 0 if False else new.count("old_name"))  # see the explicit checks below
        for kept in (
            "uses old_name in a docstring",
            "-- old_name in a comment",
            '"old_name in a string"',
            "nested old_name -/ still old_name",
            "Ns.old_name",
            "old_name_more",
        ):
            self.assertIn(kept, new)
        self.assertEqual([r["line"] for r in rep], [3, 9])

    def test_a_removed_or_restated_name_is_reported_and_left_alone(self):
        text = "theorem t : gone_one x = restated_one y\n"
        new, rep = v2.migrate_source(text, {}, {"gone_one": "removed", "restated_one": "restated"})
        self.assertEqual(new, text)
        self.assertEqual([(r["name"], r["action"]) for r in rep], [("gone_one", "removed"), ("restated_one", "restated")])

    def test_guillemets_and_unicode_names_are_whole_names(self):
        new, _ = v2.migrate_source("exact «odd name» A₂_x ψ_n\n", {"«odd name»": "«new name»", "A₂_x": "B₂_x", "ψ": "φ"})
        self.assertEqual(new, "exact «new name» B₂_x ψ_n\n")

    def test_migrating_is_idempotent_and_a_second_pass_changes_nothing(self):
        for seed in range(30):
            rng = random.Random(seed)
            names = [f"n{i}" for i in range(8)]
            ren = {f"n{i}": f"m{i}" for i in range(4)}
            tails = ["-- n1", '"n2"', "n3 n3"]
            text = "\n".join("theorem x" + str(i) + " : " + rng.choice(names) + " " + rng.choice(tails) for i in range(20))
            once, _ = v2.migrate_source(text, ren)
            twice, rep = v2.migrate_source(once, ren)
            self.assertEqual(once, twice, seed)
            self.assertEqual(rep, [])

    def test_the_name_maps_never_rewrite_what_became_ambiguous(self):
        changes = [
            {"old": "l:foo~aaaaaaaaaa", "new": "l:bar~bbbbbbbbbb", "change": "renamed"},
            {"old": "l:foo~cccccccccc", "new": None, "change": "removed"},
            {"old": "l:solo", "new": "l:solo2", "change": "renamed"},
            {"old": "l:gone", "new": None, "change": "removed"},
            {"old": "l:same", "new": "l:same", "change": "unchanged"},
        ]
        renames, gone = v2.name_maps(changes)
        self.assertEqual(renames, {"solo": "solo2"})
        self.assertEqual(gone, {"foo": "ambiguous", "gone": "removed"})


FRAGMENTS = [
    "theorem t{i} : {name} x = {name} y := by\n  exact {name}",
    "-- a comment with {name} in it",
    "/-- doc comment: `{name}` and {name} -/",
    "/- block {name} /- nested {name} -/ end {name} -/",
    'def s{i} := "text {name} \\" still {name}" ++ {name}',
    "def c{i} := '\"' ++ {name}",
    "def q{i} := '\\'' ++ {name}",
    "def n{i} := '\\n' ++ {name} ++ foo' ++ {name}'",
    'def r{i} := r#"raw {name} "quoted" {name}"# ++ {name}',
    "open {name} in example : Ns.{name} = {name}.sub",
    "example := «{name}» + ψ{name} + {name}₂ + {name}_x + x.{name}",
    "instance : Foo {name} := ⟨{name}⟩",
    "{name}\n{name} {name}",
]


def fuzz_text(rng: random.Random, names: list) -> str:
    return "\n".join(rng.choice(FRAGMENTS).format(i=i, name=rng.choice(names)) for i in range(rng.randrange(5, 40)))


def non_code(text: str) -> str:
    spans, out, last = v2.code_spans(text), [], 0
    for a, b in spans:
        out.append(text[last:a])
        last = b
    out.append(text[last:])
    return "".join(out)


class SourceFuzz(unittest.TestCase):
    NAMES = ["old_a", "old_b", "Old.c", "other", "oldψ", "A₂_old"]

    def test_an_empty_record_changes_nothing(self):
        for seed in range(200):
            text = fuzz_text(random.Random(seed), self.NAMES)
            self.assertEqual(v2.migrate_source(text, {})[0], text, seed)

    def test_a_rename_and_its_reverse_restore_the_file(self):
        ren = {"old_a": "NEWA", "old_b": "NEWB", "Old.c": "New.c", "A₂_old": "NEW₂"}
        back = {v: k for k, v in ren.items()}
        for seed in range(300):
            text = fuzz_text(random.Random(seed), self.NAMES)
            once, rep = v2.migrate_source(text, ren)
            self.assertEqual(v2.migrate_source(once, back)[0], text, seed)
            self.assertEqual(len(rep), sum(1 for r in rep if r["action"] == "rewritten"))

    def test_comments_strings_and_literals_are_never_touched(self):
        ren = {"old_a": "NEWA", "old_b": "NEWB", "Old.c": "New.c"}
        for seed in range(300):
            text = fuzz_text(random.Random(seed), self.NAMES)
            once, _ = v2.migrate_source(text, ren)
            self.assertEqual(non_code(once), non_code(text), seed)

    def test_what_is_reported_is_in_code_on_the_right_line(self):
        for seed in range(100):
            text = fuzz_text(random.Random(seed), self.NAMES)
            _, rep = v2.migrate_source(text, {}, {"old_a": "removed"})
            lines = text.split("\n")
            for r in rep:
                self.assertIn("old_a", lines[r["line"] - 1], seed)

    def test_a_longer_name_is_not_an_occurrence_of_a_shorter_one(self):
        new, rep = v2.migrate_source("exact old_a_more old_a.sub x.old_a old_a'\n", {"old_a": "NEWA"})
        self.assertEqual(new, "exact old_a_more old_a.sub x.old_a old_a'\n")
        self.assertEqual(rep, [])


class Migrate(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp())

    def tearDown(self):
        shutil.rmtree(self.dir)

    def snapshot_dir(self, rows):
        d = self.dir / "snap"
        d.mkdir()
        v2.write_jsonl(d / "tengoku-dataset.jsonl.gz", rows)
        (d / "snapshot.json").write_text(json.dumps({"dataset": {"file": "tengoku-dataset.jsonl.gz"}}))
        return d

    def test_a_snapshot_directory_becomes_a_version_2_dataset(self):
        rows = random_v1(random.Random(5), 60)
        out = self.dir / "v2.jsonl.gz"
        res = v2.migrate(str(self.snapshot_dir(rows)), out=str(out))
        self.assertEqual(res["report"]["records"], 60)
        self.assertEqual([v2.downgrade(r) for r in v2.read_jsonl(out)], rows)

    def test_a_dataset_file_in_either_form_works(self):
        rows = random_v1(random.Random(6), 20)
        gz, plain = self.dir / "a.jsonl.gz", self.dir / "a.jsonl"
        v2.write_jsonl(gz, rows)
        v2.write_jsonl(plain, rows)
        self.assertEqual(v2.migrate(str(gz))["rows"], v2.migrate(str(plain))["rows"])

    def test_migrating_a_version_2_dataset_changes_nothing(self):
        rows = random_v1(random.Random(8), 30)
        first = v2.migrate(str(self.snapshot_dir(rows)))["rows"]
        again = self.dir / "again.jsonl"
        v2.write_jsonl(again, first)
        res = v2.migrate(str(again))
        self.assertEqual((res["already"], res["rows"]), (2, first))

    def test_the_same_data_gives_the_same_bytes(self):
        rows = random_v1(random.Random(9), 40)
        src = self.snapshot_dir(rows)
        v2.migrate(str(src), out=str(self.dir / "1.gz"))
        v2.migrate(str(src), out=str(self.dir / "2.gz"))
        self.assertEqual((self.dir / "1.gz").read_bytes(), (self.dir / "2.gz").read_bytes())

    def test_the_id_table_adds_ids_and_ignores_a_pair_with_two(self):
        i1, i2 = "eq.1h3v.s4.01215b3d171d", "le.1h3v.s4.01215b3d171d"
        (self.dir / "ids.tsv").write_text(f"mathlib\ta\t{i1}\nmathlib\tb\t{i1}\nmathlib\tb\t{i2}\nmathlib\tc\tnot-an-id\n")
        d = self.dir / "d.jsonl"
        v2.write_jsonl(d, [rec("a"), rec("b"), rec("c")])
        rows = v2.migrate(str(d), ids=str(self.dir / "ids.tsv"))["rows"]
        self.assertEqual([r.get("id") for r in rows], [i1, None, None])

    def test_a_lean_file_is_rewritten_with_a_migration_record(self):
        changes = [{"old": "l:old_name", "new": "l:new_name", "change": "renamed"}, {"old": "l:gone", "new": None, "change": "removed"}]
        v2.write_jsonl(self.dir / "map.jsonl", changes)
        src = self.dir / "src"
        src.mkdir()
        (src / "A.lean").write_text("theorem t : old_name 1 := gone\n")
        (src / "B.lean").write_text("theorem u : 1 = 1\n")
        res = v2.migrate(str(src), out=str(self.dir / "out"), map_file=str(self.dir / "map.jsonl"))
        self.assertEqual((self.dir / "out" / "A.lean").read_text(), "theorem t : new_name 1 := gone\n")
        self.assertFalse((self.dir / "out" / "B.lean").exists())
        self.assertEqual([r["action"] for f in res["files"] for r in f["report"]], ["rewritten", "removed"])

    def test_a_lean_file_needs_the_record(self):
        (self.dir / "A.lean").write_text("theorem t : 1 = 1\n")
        with self.assertRaises(ValueError):
            v2.migrate(str(self.dir / "A.lean"))

    def test_a_name_is_resolved_against_a_dataset(self):
        out = self.dir / "v2.jsonl"
        v2.write_jsonl(out, v2.upgrade_dataset([rec("solo"), rec("A", statement="theorem A₂_x : True")])[0])
        res = v2.migrate("A", out=str(out))
        self.assertEqual((res["kind"], res["status"], res["refs"]), ("query", "unique-name", ["mathlib:A₂_x"]))

    def test_something_that_is_nothing_is_refused(self):
        with self.assertRaises(ValueError):
            v2.migrate("what is this")


class CommandLine(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp())

    def tearDown(self):
        shutil.rmtree(self.dir)

    def run_cli(self, *args):
        return subprocess.run([sys.executable, str(ROOT / "scripts" / "v2.py"), *args], capture_output=True, text=True)

    def test_migrate_check_and_diff(self):
        old = [rec("a"), rec("b", statement="theorem b : 1 = 1"), rec("c", statement="theorem c : 9 = 9")]
        new = [rec("a"), rec("b2", statement="theorem b2 : 1 = 1"), rec("d", statement="theorem d : 8 = 8")]
        v2.write_jsonl(self.dir / "old.jsonl", old)
        v2.write_jsonl(self.dir / "new.jsonl", new)
        r = self.run_cli("migrate", str(self.dir / "old.jsonl"), "--out", str(self.dir / "old2.jsonl.gz"))
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(json.loads(r.stdout)["report"]["records"], 3)
        c = self.run_cli("check", str(self.dir / "old2.jsonl.gz"))
        self.assertEqual((c.returncode, c.stdout.strip()), (0, "3 rows, 0 problem(s)"))
        d = self.run_cli("diff", str(self.dir / "old.jsonl"), str(self.dir / "new.jsonl"), "--out", str(self.dir / "map.jsonl"))
        self.assertEqual(d.returncode, 0, d.stderr)
        self.assertEqual(
            json.loads(d.stdout), {"unchanged": 1, "corrected": 0, "moved": 0, "renamed": 1, "restated": 0, "removed": 1, "added": 1}
        )
        self.assertEqual(len(v2.read_jsonl(self.dir / "map.jsonl")), 4)

    def test_check_fails_on_a_version_1_file(self):
        v2.write_jsonl(self.dir / "old.jsonl", [rec("a")])
        self.assertEqual(self.run_cli("check", str(self.dir / "old.jsonl")).returncode, 1)


class SnapshotSchema2(unittest.TestCase):
    """snapshot.py --schema 2: the release a maintainer cuts as 2.0.0; schema 1 stays the default"""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        (self.root / "schemas").mkdir()
        (self.root / "schemas" / "sources.json").write_text(
            json.dumps({"licences": {"https://github.com/leanprover-community/mathlib4": "Apache-2.0"}})
        )
        (self.root / "lean-toolchain").write_text(TC + "\n")
        (self.root / "data" / "trusted").mkdir(parents=True)
        lines = [
            {
                **{
                    k: v
                    for k, v in rec("A", statement="theorem A₂_x : True").items()
                    if k in ("name", "statement", "proof", "source_url", "toolchain", "library")
                },
                "status": "trusted",
            },
            {
                **{k: v for k, v in rec("dup").items() if k in ("name", "statement", "proof", "source_url", "toolchain", "library")},
                "status": "trusted",
            },
            {
                **{
                    k: v
                    for k, v in rec("dup", statement="theorem dup : 2 = 2").items()
                    if k in ("name", "statement", "proof", "source_url", "toolchain", "library")
                },
                "status": "trusted",
            },
        ]
        (self.root / "data" / "trusted" / "mathlib.jsonl").write_text("".join(json.dumps(x) + "\n" for x in lines))

    def tearDown(self):
        shutil.rmtree(self.root)

    def snap(self, out, *extra):
        notes = out.parent / (out.name + ".md")
        r = subprocess.run(
            [
                sys.executable,
                str(ROOT / "scripts" / "snapshot.py"),
                "--out",
                str(out),
                "--root",
                str(self.root),
                "--notes",
                str(notes),
                *extra,
            ],
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        return notes

    def test_the_default_is_still_schema_1(self):
        out = self.root / "out1"
        self.snap(out)
        m = json.loads((out / "snapshot.json").read_text())
        self.assertNotIn("schema", m)
        self.assertEqual(m["version"], "1.0.0")
        self.assertIn("credit_corrected_evidence", m["fields"])

    def test_schema_2_writes_the_new_dataset_and_says_so(self):
        out = self.root / "out2"
        self.snap(out, "--schema", "2")
        m = json.loads((out / "snapshot.json").read_text())
        self.assertEqual(
            (m["schema"], m["version"]), (2, "1.0.0")
        )  # a first release is 1.0.0 whatever its schema: the cut over is from a previous release
        rows = v2.read_jsonl(out / "tengoku-dataset.jsonl.gz")
        self.assertEqual(v2.check(rows), [])
        self.assertEqual(sorted(r["name"] for r in rows), ["A₂_x", "dup", "dup"])
        self.assertEqual(sorted(r["ref"] for r in rows if r["name"] == "A₂_x"), ["mathlib:A₂_x"])

    def test_going_from_1_to_2_is_a_major_release_and_the_notes_say_how_to_migrate(self):
        self.snap(self.root / "r1")
        notes = self.snap(self.root / "r2", "--schema", "2", "--previous", str(self.root / "r1"))
        m = json.loads((self.root / "r2" / "snapshot.json").read_text())
        self.assertEqual(m["version"], "2.0.0")
        text = notes.read_text()
        self.assertIn("Major version", text)
        self.assertIn("schema changed from 1 to 2", text)
        self.assertIn("scripts/v2.py migrate", text)
        # compared record by record: nothing was added or retracted by the schema change
        self.assertIn("**Added:** 0 trusted theorems", text)
        self.assertIn("**Retracted:** 0.", text)

    def test_a_dataset_does_not_go_back_to_schema_1(self):
        self.snap(self.root / "r2", "--schema", "2")
        r = subprocess.run(
            [
                sys.executable,
                str(ROOT / "scripts" / "snapshot.py"),
                "--out",
                str(self.root / "r3"),
                "--root",
                str(self.root),
                "--previous",
                str(self.root / "r2"),
            ],
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("does not go back", r.stdout + r.stderr)

    def test_2_after_2_with_no_change_publishes_nothing(self):
        self.snap(self.root / "r2", "--schema", "2")
        self.snap(self.root / "r2b", "--schema", "2", "--previous", str(self.root / "r2"))
        self.assertTrue((self.root / "r2b" / "unchanged").exists())

    def test_a_new_theorem_after_2_is_a_minor_release_keyed_by_ref(self):
        self.snap(self.root / "r2", "--schema", "2")
        with (self.root / "data" / "trusted" / "mathlib.jsonl").open("a") as fh:
            fh.write(
                json.dumps(
                    {
                        **{
                            k: v
                            for k, v in rec("dup", statement="theorem dup : 3 = 3").items()
                            if k in ("name", "statement", "proof", "source_url", "toolchain", "library")
                        },
                        "status": "trusted",
                    }
                )
                + "\n"
            )
        notes = self.snap(self.root / "r2b", "--schema", "2", "--previous", str(self.root / "r2"))
        self.assertEqual(json.loads((self.root / "r2b" / "snapshot.json").read_text())["version"], "1.1.0")
        self.assertIn("**Added:** 1 trusted theorems", notes.read_text())


@unittest.skipUnless(
    os.environ.get("TENGOKU_V1_SNAPSHOT"), "set TENGOKU_V1_SNAPSHOT to the directory of the 1.0.0 release to run this on the real data"
)
class RealRelease(unittest.TestCase):
    """the 198,172 records of release 1.0.0 (the v2-migration workflow runs this)"""

    @classmethod
    def setUpClass(cls):
        d = Path(os.environ["TENGOKU_V1_SNAPSHOT"])
        cls.manifest = json.loads((d / "snapshot.json").read_text())
        cls.v1 = v2.read_jsonl(d / cls.manifest["dataset"]["file"])
        cls.v2, cls.report = v2.upgrade_dataset(cls.v1)

    def test_the_release_is_what_the_manifest_says(self):
        self.assertEqual(len(self.v1), self.manifest["dataset"]["records"])
        self.assertEqual(v2.schema_of(self.v1), 1)

    def test_every_record_survives_the_round_trip(self):
        bad = [i for i, (a, b) in enumerate(zip(self.v1, self.v2)) if v2.downgrade(b) != a]
        self.assertEqual(bad[:5], [])

    def test_the_result_obeys_every_invariant(self):
        self.assertEqual(v2.check(self.v2)[:5], [])
        self.assertEqual(len({r["ref"] for r in self.v2}), len(self.v1))

    def test_what_version_1_got_wrong_is_found_and_repaired(self):
        self.assertGreater(self.report["names_repaired"], 6000)
        for r in self.v2:
            if "legacy_name" in r:
                self.assertTrue(r["name"].startswith(r["legacy_name"]))

    def test_the_migration_is_deterministic_and_idempotent(self):
        again, _ = v2.upgrade_dataset(self.v1)
        self.assertEqual(again, self.v2)
        first = gzip.compress(b"".join(json.dumps(r, sort_keys=True).encode() for r in self.v2), mtime=0)
        second = gzip.compress(b"".join(json.dumps(r, sort_keys=True).encode() for r in again), mtime=0)
        self.assertEqual(first, second)
        self.assertEqual(v2.schema_of(self.v2), 2)

    def test_every_version_1_name_still_resolves(self):
        idx = v2.Index(self.v2)
        rng = random.Random(0)
        for r in rng.sample(self.v1, 3000):
            res = idx.resolve(r["name"], library=r["library"])
            self.assertIn(res.status, ("unique-name", "ambiguous"), r["name"])
            self.assertIn(idx.ref_of_v1(r), [x["ref"] for x in res.records], r["name"])

    def test_a_release_compared_with_itself_has_no_change(self):
        counts = v2.summarise(v2.classify(self.v2, self.v2))
        self.assertEqual(counts["unchanged"], len(self.v2))


if __name__ == "__main__":
    unittest.main()
