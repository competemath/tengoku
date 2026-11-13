"""A `:=` that belongs to a `let`/`letI`/`have`/`haveI` of the TYPE is not the proof's `:=`, and a theorem defined by match arms ends its statement at its first arm.

The real case: the batch-7 records PR (competemath/tengoku#794, 13 Nov 2026), Gitar's review: `tools/lean_extract.py::_find_statement_end` stopped at the first `:=` at depth 0, so
`theorem isometry_left (a : CommonAmbient X Y) :\\n    letI := a.metric\\n    Isometry a.left := by ...` was recorded with the statement `... :\\n    letI` and the claim's end at the start of `proof`.
Measured on the harvested records before the fix: 248 of 54,049 records of batch 7 and 510 of 58,822 of the batches already merged (Etingof 75, lean-operads 159, nlalib 191, abel 43, lean-eval 35,
rankamplificationtotient 6, ck-hopf 1) ended their statement inside such a binder.

The fixture (fixtures/real-let-binder-records-2026-11-13.json.gz) holds, from 14 real libraries as harvested before the fix: the 758 records whose statement ends in a let/have/set/obtain fragment (proofs cut to 4,000
characters) and a 3.5% sample (3,944) of the others (proofs cut to 200 characters). A record is put back together as `statement + " " + proof` and extracted again.

Invariants:
  1. Nothing is lost: for every real record the new statement plus the new proof is the old statement plus the old proof, up to whitespace.
  2. Every real record that ended in a let/have binder (615 of the 758) now ends its statement after the claim. The new and the old statement are one a prefix of the other: the new one is longer when the old
     one stopped inside the type, and shorter when the old one had swallowed the arms of a theorem defined by match arms.
  3. A real record the old code split right is split the same way (3,905 of the 3,944 sampled; 5 cannot be split from the 200 characters of proof the fixture keeps; the 34 others were wrong before:
     11 cut at a binder, 23 that had swallowed their match arms).
     Known limit, unchanged: a theorem defined by match arms whose arms hold a `:=` of a keyword that is not a binder (`obtain`, `set`) is still cut inside an arm (about 90 of the 758).
  4. 5,000 generated declarations with 0 to 4 binders of the four kinds, nested brackets, default arguments, comments and identifiers that contain the keywords: the statement is exactly the text before the
     declaration's own `:=`.
  5. Mutants: the pattern that finds binders removed, and the proof-end pattern as it was (a match arm at column 0 ended the proof) each fail a real check."""

from __future__ import annotations

import gzip
import importlib.util
import json
import random
import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("lean_extract", ROOT / "tools" / "lean_extract.py")
le = importlib.util.module_from_spec(spec)
sys.modules["lean_extract"] = le  # dataclasses resolve the module through sys.modules
spec.loader.exec_module(le)

REAL = json.loads(gzip.open(Path(__file__).resolve().parent / "fixtures" / "real-let-binder-records-2026-11-13.json.gz", "rt").read())
BINDER_LINE = re.compile(r"^\s*(?:letI|haveI|let|have)\b")
MATCH_ARM = re.compile(r"\n[ \t]*\|[^\n]*=>")
ENDS_IN_BINDER = re.compile(r"^(?:letI|haveI|let|have)\b[^:=]*$")


def squash(s: str) -> str:
    return re.sub(r"\s+", "", s)


def split(record: dict):
    decls = le.extract_declarations(record["statement"] + " " + record["proof"])
    return next((d for d in decls if d.name in (record["name"], record["name"].split(".")[-1])), decls[0] if decls else None)


def ends_in_binder(statement: str) -> bool:
    last = statement.rstrip().splitlines()[-1].strip() if statement.strip() else ""
    return bool(ENDS_IN_BINDER.match(last))


class RealRecords(unittest.TestCase):
    def test_the_fixture_is_the_real_one(self):
        self.assertEqual(len(REAL["truncated"]), 758)
        self.assertEqual(len(REAL["normal"]), 3944)
        self.assertEqual(
            {r["lib"] for r in REAL["truncated"]},
            {
                "finite-simple-groups-lean",
                "lean-commutator",
                "piirrationalitymeasure",
                "sandrones-library",
                "tda-lib",
                "twinprime",
                "ck-hopf-formalization",
                "nlalib",
                "lean-eval-pi-succ-sphere-n-mulequiv-zmod-two",
                "rankamplificationtotient",
                "etingofrepresentationtheory",
                "abel-formalization",
                "lean-operads",
            },
        )

    def test_the_truncated_records_are_split_after_the_claim_and_nothing_is_lost(self):
        grew = binder_ending_before = 0
        for r in REAL["truncated"]:
            d = split(r)
            self.assertIsNotNone(d, r["name"])
            self.assertEqual(squash(d.statement + d.proof), squash(r["statement"] + r["proof"]), r["name"])  # 1
            a, b = squash(d.statement), squash(r["statement"])
            self.assertTrue(a.startswith(b) or b.startswith(a), r["name"])  # 2
            if ends_in_binder(r["statement"]):
                binder_ending_before += 1
                self.assertFalse(ends_in_binder(d.statement), r["name"])
            grew += len(d.statement) > len(r["statement"])
        self.assertGreaterEqual(binder_ending_before, 600)
        self.assertGreaterEqual(grew, 600)  # the rest are cut inside a match arm of a theorem defined by arms, a limit this change leaves

    def test_the_records_the_old_code_split_right_are_split_the_same_way(self):
        same = changed = 0
        for r in REAL["normal"]:
            d = split(r)
            if d is None:  # the fixture's proofs are cut to 200 characters: a truncated record's own `:=` may lie beyond
                continue
            if d.statement == r["statement"]:
                same += 1
                continue
            changed += 1
            self.assertEqual(squash(d.statement + d.proof)[:150], squash(r["statement"] + r["proof"])[:150], r["name"])
            a, b = squash(d.statement), squash(r["statement"])
            self.assertTrue(a.startswith(b) or b.startswith(a), r["name"])
            last = r["statement"].rstrip().splitlines()[-1]
            self.assertTrue(BINDER_LINE.match(last) or MATCH_ARM.search(r["statement"]), r["name"])  # it was a truncation too
        self.assertEqual((same, changed), (3905, 34))

    def test_gitars_example(self):
        (d,) = le.extract_declarations(
            "theorem CommonAmbient.isometry_left (a : CommonAmbient X Y) :\n    letI := a.metric\n    Isometry a.left := by\n  let : MetricSpace a.carrier := a.metric\n  exact Isometry.of_dist_eq fun _ _ => rfl\n"
        )
        self.assertEqual(
            d.statement, "theorem CommonAmbient.isometry_left (a : CommonAmbient X Y) :\n    letI := a.metric\n    Isometry a.left"
        )
        self.assertTrue(d.proof.startswith(":= by\n  let : MetricSpace"))


class Cases(unittest.TestCase):
    def one(self, src: str):
        (d,) = le.extract_declarations(src)
        return d

    def test_a_let_in_the_type_owns_its_assignment(self):
        d = self.one("theorem t : let N := 3; N = 3 := by decide\n")
        self.assertEqual((d.statement, d.proof), ("theorem t : let N := 3; N = 3", ":= by decide"))

    def test_several_binders_of_every_kind(self):
        d = self.one(
            "theorem t (h : 0 < n) :\n    let a := f n\n    letI : Foo := inst\n    have h2 : a = a := rfl\n    haveI := bar\n    a = a := by\n  simp\n"
        )
        self.assertTrue(d.statement.endswith("haveI := bar\n    a = a"))
        self.assertTrue(d.proof.startswith(":= by\n  simp"))

    def test_a_binder_inside_brackets_is_not_counted_and_nor_is_a_default_argument(self):
        d = self.one("theorem t (n : Nat := 0) : (let x := 1; x) = 1 := rfl\n")
        self.assertEqual(d.statement, "theorem t (n : Nat := 0) : (let x := 1; x) = 1")

    def test_names_that_contain_the_keywords_are_not_binders(self):
        for ident in ("letter", "let'", "my.have", "have_h", "haveI'", "Let", "letI!"):
            d = self.one(f"theorem t : P {ident} = Q := by\n  simp\n")
            self.assertEqual(d.statement, f"theorem t : P {ident} = Q", ident)

    def test_set_and_obtain_are_not_binders_of_a_type(self):
        d = self.one("theorem t (set : Finset Nat) : set = set := rfl\n")
        self.assertEqual(d.statement, "theorem t (set : Finset Nat) : set = set")

    def test_a_comment_cannot_hide_or_fake_a_binder(self):
        d = self.one("theorem t : P := by\n  -- let x := 1\n  simp\n")
        self.assertEqual(d.statement, "theorem t : P")
        d = self.one("theorem t : -- let x := 1 here\n    P := by\n  simp\n")
        self.assertEqual(squash(d.statement), "theoremt:P")

    def test_a_theorem_defined_by_match_arms_ends_its_statement_at_the_first_arm(self):
        d = self.one("theorem t : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | n + 1 => by\n      simp\n")
        self.assertEqual(d.statement, "theorem t : ∀ n : Nat, n + 0 = n")
        self.assertTrue(d.proof.startswith("| 0 => rfl"))
        self.assertIn("simp", d.proof)

    def test_known_limit_an_arm_with_a_non_binder_assignment_still_cuts_the_statement(self):
        """unchanged by this change (about 90 of the 758 real records): `obtain ... := e` in an arm is the first `:=` the scan meets that is not a binder's"""
        d = self.one("theorem t : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | n + 1 => by\n      obtain ⟨a, b⟩ := foo n\n      simp\n")
        self.assertTrue(d.statement.endswith("obtain ⟨a, b⟩"))

    def test_have_and_let_in_arms_are_consumed_as_binders_so_the_statement_still_ends_at_the_first_arm(self):
        d = self.one(
            "theorem t : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | n + 1 => by\n      have h := foo n\n      let q := n\n      simp\n"
        )
        self.assertEqual(d.statement, "theorem t : ∀ n : Nat, n + 0 = n")

    def test_match_arms_with_a_let_in_the_type_and_arms_at_column_zero(self):
        d = self.one("theorem t : ∀ p : Nat,\n    let a := p\n    a = p\n| 0 => rfl\n| p + 1 => by\n    let q := p\n    rfl\n")
        self.assertEqual(squash(d.statement), squash("theorem t : ∀ p : Nat, let a := p a = p"))
        self.assertIn("let q := p", d.proof)

    NEXT = (
        "theorem u : True := trivial",
        "lemma u : True := trivial",
        "noncomputable def pathTab0 (x : Nat) : List Nat := []",
        "private def f : Nat := 1",
        "instance : Inhabited Foo := ⟨x⟩",
        "/-- A docstring. -/\ntheorem u : True := trivial",
        "@[simp] theorem u : True := trivial",
        "end Foo",
        "namespace Bar",
        "open Nat in\ntheorem u : True := trivial",
        "#check t",
        "variable (x : Nat)",
    )

    def test_an_arm_theorem_followed_by_another_command_does_not_take_it_in(self):
        """Gitar on #811: in a real file an arm theorem is followed by something; before, it swallowed the next declaration's `:=`, or ended at an empty proof"""
        arms = "theorem t : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | n + 1 => rfl\n"
        for nxt in self.NEXT:
            for gap in ("", "\n", "\n\n"):
                ds = le.extract_declarations(arms + gap + nxt + "\n")
                t = next(d for d in ds if d.name == "t")
                self.assertEqual(t.statement, "theorem t : ∀ n : Nat, n + 0 = n", nxt)
                self.assertTrue(t.proof.startswith("| 0 => rfl"), nxt)
                self.assertNotIn("def", t.statement + t.proof, nxt)
                self.assertNotIn("True", t.statement + t.proof, nxt)

    def test_the_declaration_after_an_arm_theorem_is_extracted_whole(self):
        arms = "theorem t : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | n + 1 => rfl\n\n"
        ds = le.extract_declarations(arms + "theorem u : True := trivial\n")
        self.assertEqual([(d.name, d.statement, d.proof) for d in ds if d.name == "u"], [("u", "theorem u : True", ":= trivial")])

    def test_arms_at_column_zero_followed_by_another_command(self):
        for nxt in self.NEXT:
            ds = le.extract_declarations("theorem t : ∀ p : Nat, p = p\n| 0 => rfl\n| p + 1 => by\n    let q := p\n    rfl\n" + nxt + "\n")
            t = next(d for d in ds if d.name == "t")
            self.assertEqual(t.statement, "theorem t : ∀ p : Nat, p = p", nxt)
            self.assertIn("let q := p", t.proof, nxt)

    def test_a_declaration_with_a_proof_of_its_own_never_takes_an_arm_for_its_end(self):
        d = self.one("theorem t : f = fun x => x := by\n  intro x\n  match x with\n  | 0 => rfl\n  | _ => rfl\n")
        self.assertEqual(d.statement, "theorem t : f = fun x => x")

    def test_unterminated_is_skipped(self):
        self.assertEqual(le.extract_declarations("theorem t : let a := 1\n  a = 1\n"), [])


def generated(rnd: random.Random):
    """(source, statement, proof) of a random declaration: binders of the four kinds, each with its own `:=`, in the type"""
    name = f"t{rnd.randint(0, 99999)}"
    binders = []
    for _ in range(rnd.randint(0, 4)):
        kind = rnd.choice(["let", "letI", "have", "haveI"])
        value = rnd.choice(["3", "inst", "(f x)", "⟨a, b⟩", "fun x => x", "(g (n := 0))", "by decide"])
        ident = rnd.choice(["x", "N", "h", "_", "x'", "xₙ", "«a b»"])
        binders.append(f"{kind} {ident} : T := {value}" if kind in ("let", "have") and rnd.random() < 0.5 else f"{kind} {ident} := {value}")
    pre = rnd.choice(["", " (n : Nat := 0)", " {a b : Nat} (h : (let y := 1; y) = 1)", " [inst : Foo (α := Nat)]"])
    claim = rnd.choice(["P n", "∀ k, f k = g k", "a = b ∧ c ≤ d", "(fun x => x + 1) 0 = 1", "x = if y then 1 else 2"])
    sep = rnd.choice(["\n    ", "; ", "\n      "])
    typ = f"{sep}".join(binders + [claim]) if binders else claim
    statement = f"theorem {name}{pre} :{rnd.choice([' ', chr(10) + '    '])}{typ}"
    proof = ":= " + rnd.choice(["rfl", "by\n  simp", "by\n  have h := foo\n  let y := 2\n  exact h", "fun x => x"])
    return statement + " " + proof + "\n", statement, proof


class Generated(unittest.TestCase):
    def test_5000_declarations(self):
        rnd = random.Random(20261113)
        with_binders = 0
        for _ in range(5000):
            src, statement, proof = generated(rnd)
            (d,) = le.extract_declarations(src)
            self.assertEqual((d.statement, d.proof), (statement.strip(), proof.strip()), src)
            with_binders += bool(re.search(r"\b(?:let|letI|have|haveI)\b [^(]", statement))
        self.assertGreater(with_binders, 3500)


class Mutants(unittest.TestCase):
    def test_without_the_binder_pattern_the_real_example_is_cut_again(self):
        original = le._TYPE_BINDER_RE
        le._TYPE_BINDER_RE = re.compile(r"(?!)")
        try:
            cut = [r for r in REAL["truncated"] if (d := split(r)) is not None and ends_in_binder(d.statement)]
            self.assertGreaterEqual(len(cut), 600)  # what the harvest did
            (d,) = le.extract_declarations("theorem t : let N := 3; N = 3 := by decide\n")
            self.assertEqual(d.statement, "theorem t : let N")
        finally:
            le._TYPE_BINDER_RE = original

    def test_with_the_proof_end_as_it_was_a_match_arm_at_column_zero_loses_text(self):
        original = le._TOP_LEVEL_LINE_RE
        le._TOP_LEVEL_LINE_RE = re.compile(r"^[^\s].*$", re.MULTILINE)
        try:
            (d,) = le.extract_declarations("theorem t : ∀ p : Nat, p = p\n| 0 => rfl\n| p + 1 => rfl\n")
            self.assertNotIn("p + 1", d.proof)
        finally:
            le._TOP_LEVEL_LINE_RE = original
        (d,) = le.extract_declarations("theorem t : ∀ p : Nat, p = p\n| 0 => rfl\n| p + 1 => rfl\n")
        self.assertIn("p + 1", d.proof)

    def test_without_the_stop_at_the_next_command_an_arm_theorem_swallows_it(self):
        src = "theorem t : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | n + 1 => rfl\n\ndef f : Nat := 1\n"
        (t,) = [d for d in le.extract_declarations(src) if d.name == "t"]
        self.assertEqual(t.statement, "theorem t : ∀ n : Nat, n + 0 = n")
        original = le._TOP_LEVEL_LINE_RE
        # the stop reads this pattern; a pattern that never matches is the code before the fix
        le._TOP_LEVEL_LINE_RE = re.compile(r"(?!)")
        try:
            (t2,) = [d for d in le.extract_declarations(src) if d.name == "t"]
            self.assertIn("def f", t2.statement)
        finally:
            le._TOP_LEVEL_LINE_RE = original

    def test_without_the_arm_fallback_an_arm_theorem_with_a_let_is_skipped(self):
        src = "theorem t : ∀ p : Nat,\n    let a := p\n    a = p\n  | 0 => rfl\n  | p + 1 => rfl\n"
        self.assertEqual(len(le.extract_declarations(src)), 1)
        original = le._MATCH_ARM_RE
        le._MATCH_ARM_RE = re.compile(r"(?!)")
        try:
            self.assertEqual(le.extract_declarations(src), [])
        finally:
            le._MATCH_ARM_RE = original


if __name__ == "__main__":
    unittest.main()
