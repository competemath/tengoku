import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import stats


def write(p: Path, lines):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("".join(json.dumps(l) + "\n" for l in lines))


class StatsTest(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        write(
            self.root / "data/trusted/alpha.jsonl",
            [{"name": "a", "promoted_at": "2026-09-01T00:00:00Z"}, {"name": "b", "promoted_at": "2026-09-13T10:00:00Z"}],
        )
        write(self.root / "data/staging/alpha.jsonl", [{"name": "c"}])
        write(self.root / "data/tentative/beta.jsonl", [{"name": "d"}, {"name": "e"}, {"name": "f"}])
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n")

    def test_counts_per_library_and_tier(self):
        s = stats.collect(self.root)
        self.assertEqual(s["libraries"]["alpha"]["trusted"], 2)
        self.assertEqual(s["libraries"]["alpha"]["staging"], 1)
        self.assertEqual(s["libraries"]["alpha"]["tentative"], 0)
        self.assertEqual(s["libraries"]["beta"]["tentative"], 3)
        self.assertEqual(s["totals"], {"trusted": 2, "staging": 1, "tentative": 3, "all": 6, "tentative_already_trusted": 0})
        self.assertEqual(s["library_count"], 2)

    def test_last_promoted_is_the_newest_timestamp(self):
        s = stats.build(self.root)
        self.assertEqual(s["libraries"]["alpha"]["last_promoted_at"], "2026-09-13T10:00:00Z")
        self.assertEqual(s["last_promoted_at"], "2026-09-13T10:00:00Z")
        self.assertEqual(s["toolchain"], "leanprover/lean4:v4.34.0-rc2")
        self.assertRegex(s["generated_at"], r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")

    def test_a_factory_bundles_theorems_count_as_trusted(self):
        """An intake library has no records: its manifest's lines are its trusted theorems (16,699 in 23 libraries were invisible, 2026-10-07)."""
        write(self.root / "data/intake/gamma/manifest.jsonl", [{"name": "g1"}, {"name": "g2"}, {"name": "g3"}])
        write(self.root / "data/intake/alpha/manifest.jsonl", [{"name": "a-in-a-bundle"}])  # records and a bundle: both count
        s = stats.collect(self.root)
        self.assertEqual(
            (s["libraries"]["gamma"]["trusted"], s["libraries"]["gamma"]["intake"], s["libraries"]["gamma"]["staging"]), (3, 3, 0)
        )
        self.assertEqual((s["libraries"]["alpha"]["trusted"], s["libraries"]["alpha"]["intake"]), (3, 1))
        self.assertEqual(s["totals"], {"trusted": 6, "staging": 1, "tentative": 3, "all": 10, "tentative_already_trusted": 0})
        self.assertEqual(s["library_count"], 3)
        self.assertNotIn("intake", s["libraries"]["beta"])

    def test_a_tentative_record_the_tree_already_trusts_is_counted_once(self):
        """Tentative files are append-only: a record stays when its library arrives as a bundle (same statement, bare name) and
        when it is promoted (same name; the trusted copy may drop an attribute). Either way it is one theorem, counted as trusted."""
        write(
            self.root / "data/tentative/delta.jsonl",
            [
                {"name": "lemma1", "statement": "theorem lemma1 (n : ℕ) :\n    n + 0 = n"},
                {"name": "lemma2", "statement": "@[simp] theorem lemma2 : True"},
                {"name": "lemma3", "statement": "theorem lemma3 : 1 = 1"},
                {"name": "lemma4", "statement": "theorem lemma4 : 4 = 4"},
            ],
        )
        write(
            self.root / "data/intake/delta/manifest.jsonl",
            [
                {"name": "Delta.lemma1", "statement": "theorem lemma1 (n : ℕ) : n + 0 = n"},  # the bundle: whitespace aside, the same
                {"name": "Delta.extra", "statement": "theorem extra : 2 = 2"},  # only in the bundle
            ],
        )
        write(
            self.root / "data/trusted/delta.jsonl",
            [{"name": "lemma2", "statement": "theorem lemma2 : True", "promoted_at": "2026-10-01T00:00:00Z"}],
        )
        s = stats.collect(self.root)
        d = s["libraries"]["delta"]
        self.assertEqual((d["trusted"], d["intake"], d["tentative"], d["tentative_already_trusted"]), (3, 2, 2, 2))
        self.assertEqual(s["totals"], {"trusted": 5, "staging": 1, "tentative": 5, "all": 11, "tentative_already_trusted": 2})
        self.assertNotIn("tentative_already_trusted", s["libraries"]["beta"])  # nothing trusted to compare with

    def test_each_trusted_theorem_accounts_for_one_tentative_record_only(self):
        """The same statement in two namespaces, or a name repeated in a file, is not removed more often than the tree holds it."""
        write(
            self.root / "data/tentative/eps.jsonl",
            [
                {"name": "lemma1", "statement": "theorem lemma1 : True"},  # one namespace's
                {"name": "lemma1", "statement": "theorem lemma1 : True"},  # another namespace's: a different theorem
                {"name": "dup", "statement": "theorem dup : 1 = 1"},
                {"name": "dup", "statement": "theorem dup : 2 = 2"},  # a different theorem under the same bare name
            ],
        )
        write(self.root / "data/intake/eps/manifest.jsonl", [{"name": "A.lemma1", "statement": "theorem lemma1 : True"}])
        write(self.root / "data/trusted/eps.jsonl", [{"name": "dup", "statement": "theorem dup : 1 = 1"}])
        s = stats.collect(self.root)
        e = s["libraries"]["eps"]
        self.assertEqual((e["trusted"], e["tentative"], e["tentative_already_trusted"]), (2, 2, 2))

    def test_a_last_line_without_a_newline_is_no_record_for_the_count_or_the_subtraction(self):
        """count_lines counts newlines, so the subtraction must read records by the same boundary: no negative tentative count."""
        write(
            self.root / "data/intake/zeta/manifest.jsonl",
            [{"name": "Z.a", "statement": "theorem a : True"}, {"name": "Z.b", "statement": "theorem b : True"}],
        )
        tentative = self.root / "data/tentative/zeta.jsonl"
        tentative.parent.mkdir(parents=True, exist_ok=True)
        tentative.write_text(
            json.dumps({"name": "a", "statement": "theorem a : True"}) + "\n" + json.dumps({"name": "b", "statement": "theorem b : True"})
        )  # the second record has no newline
        s = stats.collect(self.root)
        z = s["libraries"]["zeta"]
        self.assertEqual((z["tentative"], z["tentative_already_trusted"]), (0, 1))
        self.assertGreaterEqual(s["totals"]["tentative"], 0)

    def corrected(self):
        """A manifest theorem and its tentative record, harvested cut at the `:=` of a let (tengoku#811), with its correction appended."""
        full = "theorem t : let n := 1; n = 1"
        write(self.root / "data/intake/eta/manifest.jsonl", [{"name": "E.t", "statement": full}])
        cut = {"name": "t", "statement": "theorem t : let n", "proof": ":= 1; n = 1 := rfl"}
        fix = {"statement_correction": "t", "statement": full, "proof": ":= rfl", "reason": "cut at a let", "by": "t", "at": "2026-11-13"}
        write(self.root / "data/tentative/eta.jsonl", [cut, {"name": "u", "statement": "theorem u : True", "proof": ":= trivial"}, fix])
        return fix

    def test_a_statement_correction_is_not_a_second_record(self):
        self.corrected()
        s = stats.collect(self.root)
        e = s["libraries"]["eta"]
        self.assertEqual(e["tentative"] + e["tentative_already_trusted"], 2)  # t and u, not three lines
        self.assertEqual(s["totals"]["tentative"], 3 + e["tentative"])

    def test_the_correction_text_is_what_a_record_is_matched_by(self):
        """The cut record never matched the manifest's statement; with its correction it is the theorem the tree already holds."""
        self.corrected()
        e = stats.collect(self.root)["libraries"]["eta"]
        self.assertEqual(e["tentative_already_trusted"], 1)
        self.assertEqual(e["tentative"], 1)

    def test_the_newest_correction_wins_and_only_its_own_name(self):
        fix = self.corrected()
        tentative = self.root / "data/tentative/eta.jsonl"
        with tentative.open("a") as f:
            f.write(json.dumps({**fix, "statement": "theorem t : let n", "proof": ":= 1; n = 1 := rfl"}) + "\n")  # back to the cut text
        recs = {r["name"]: r for r in stats.iter_records(tentative)}
        self.assertEqual(sorted(recs), ["t", "u"])
        self.assertEqual(recs["t"]["statement"], "theorem t : let n")
        self.assertEqual(recs["u"]["statement"], "theorem u : True")
        self.assertEqual(stats.collect(self.root)["libraries"]["eta"]["tentative_already_trusted"], 0)

    def test_a_correction_line_without_its_newline_is_nothing_for_both(self):
        self.corrected()
        tentative = self.root / "data/tentative/eta.jsonl"
        tentative.write_text(tentative.read_text().rstrip("\n"))  # the last line, the correction, has no newline
        e = stats.collect(self.root)["libraries"]["eta"]
        self.assertEqual(e["tentative"] + e["tentative_already_trusted"], 2)
        self.assertEqual(e["tentative_already_trusted"], 0)

    def test_the_word_alone_in_a_records_text_is_no_correction(self):
        write(
            self.root / "data/tentative/eta.jsonl",
            [{"name": "w", "statement": "theorem w : True", "proof": ":= by simp -- statement_correction"}],
        )
        self.assertEqual(stats.collect(self.root)["libraries"]["eta"]["tentative"], 1)

    def test_empty_tree(self):
        empty = Path(tempfile.mkdtemp())
        s = stats.collect(empty)
        self.assertEqual(s["totals"]["all"], 0)
        self.assertEqual(s["libraries"], {})


if __name__ == "__main__":
    unittest.main()
