"""scripts/isnad_tag.py: writing tags into Lean files, taking them out, and the equivalence law. The ranges are the real ones: `tools/isnad/tagger/ranges.json` is what
`tengoku-isnad --ranges` printed for `tools/isnad/tagger/Fixture.lean` (CI: pr-tests, job isnad, compares a fresh run against it)."""

import importlib.util
import json
import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location("isnad_tag", ROOT / "scripts" / "isnad_tag.py")
tag = importlib.util.module_from_spec(spec)
sys.modules["isnad_tag"] = tag
spec.loader.exec_module(tag)

FIXTURE = (ROOT / "tools" / "isnad" / "tagger" / "Fixture.lean").read_text(encoding="utf-8")
RANGES = json.loads((ROOT / "tools" / "isnad" / "tagger" / "ranges.json").read_text(encoding="utf-8"))
TAG = "@isnad1 id=eq.0h2v.s4.05598c1b76c4 from=seed src=0 shape=900bc7c0 vocab=fc0e7020"
OTHER = "@isnad1 id=eq.0h0v.s0.000000000000 from=novel src=0 shape=00000000 vocab=00000000"


def items(names=None, the_tag=TAG):
    return [tag.Item(n, tuple(v["range"]), tuple(v["sel"]), the_tag) for n, v in RANGES.items() if names is None or n in names]


def block(text, name):
    """The command of `name` in `text` (from its docstring to its `:=`), found by its declared name."""
    i = text.index(name.split(".")[-1].replace("«", "").replace("»", ""))
    start = max(text.rfind("\n\n", 0, i), text.rfind("\nend\n", 0, i), text.rfind("\nsection\n", 0, i))
    return text[start:i]


class Fixture(unittest.TestCase):
    def test_every_range_points_at_its_theorem_name(self):
        # the fixture and its ranges belong together: the text at each selection range is the declared name
        for name, v in RANGES.items():
            s0, s1 = tag.offset_of(FIXTURE, v["sel"][0], v["sel"][1]), tag.offset_of(FIXTURE, v["sel"][2], v["sel"][3])
            self.assertTrue(tag.declared_name_matches(name, FIXTURE[s0:s1]), (name, FIXTURE[s0:s1]))

    def test_every_command_range_starts_at_its_docstring_attribute_or_keyword(self):
        for name, v in RANGES.items():
            p = tag.offset_of(FIXTURE, v["range"][0], v["range"][1])
            self.assertTrue(
                FIXTURE.startswith(("/--", "@[", "theorem", "protected theorem"), p),
                (name, FIXTURE[p : p + 20]),
            )


class Tagging(unittest.TestCase):
    def setUp(self):
        self.new, self.counts, self.skipped = tag.tag_text(FIXTURE, items())

    def test_all_twelve_are_tagged_none_skipped(self):
        self.assertEqual(self.skipped, [])
        self.assertEqual(self.counts, {"added": 5, "replaced": 1, "same": 0, "created": 6})
        self.assertEqual(self.new.count("@isnad1 id="), 12)

    def test_one_line_doc(self):
        self.assertIn(f"/-- one line\n{TAG}\n-/\ntheorem one_line", self.new)

    def test_many_lines_doc_gets_the_tag_as_its_last_line(self):
        self.assertIn(f"/-- many\nlines of doc\n{TAG}\n-/\ntheorem many_lines", self.new)

    def test_doc_and_attribute(self):
        self.assertIn(f"/-- ends with text.\n{TAG}\n-/\n@[simp]\ntheorem with_attr", self.new)

    def test_no_doc_creates_one_before_the_command(self):
        self.assertIn(f"/--\n{TAG}\n-/\ntheorem no_doc", self.new)

    def test_no_doc_with_an_inline_attribute_goes_before_the_attribute(self):
        self.assertIn(f"/--\n{TAG}\n-/\n@[simp] theorem inline_attr", self.new)

    def test_a_nested_comment_in_the_doc_is_kept_whole(self):
        self.assertIn(f"/-- nested /- comment -/ inside the doc\n{TAG}\n-/\ntheorem nested", self.new)

    def test_protected_dotted_name(self):
        self.assertIn(f"/--\n{TAG}\n-/\nprotected theorem Nat'.dotted", self.new)

    def test_indented_commands_get_indented_tag_lines(self):
        self.assertIn(f"  /-- indented doc\n  {TAG}\n  -/\n  theorem indented ", self.new)
        self.assertIn(f"  /--\n  {TAG}\n  -/\n  theorem indented_nodoc", self.new)

    def test_guillemets_and_unicode_names(self):
        self.assertIn(f"/--\n{TAG}\n-/\ntheorem «weird name»", self.new)
        self.assertIn(f"/--\n{TAG}\n-/\ntheorem unicode_τ", self.new)

    def test_an_old_tag_is_replaced_not_duplicated(self):
        self.assertIn(f"/-- a docstring with a tag line already:\n{TAG}\n-/\ntheorem already_tagged", self.new)
        self.assertNotIn(OTHER, self.new)

    def test_a_second_pass_changes_nothing(self):
        # the positions of the first pass are stale for a moved file, so re-ranging is the caller's job: here the same text is tagged with its own ranges again
        again, counts, skipped = tag.tag_text(self.new, [])
        self.assertEqual((again, skipped), (self.new, []))
        self.assertEqual(sum(counts.values()), 0)

    def test_the_same_tag_in_a_doc_is_left_alone(self):
        doc = f"/-- d\n{TAG}\n-/"
        self.assertEqual(tag.with_tag(doc, TAG), (doc, "same"))
        doc1 = f"/-- d\n{TAG}-/"
        self.assertEqual(tag.with_tag(doc1, TAG), (doc1, "same"))

    def test_replacing_keeps_the_indent_of_the_closing(self):
        self.assertEqual(tag.with_tag(f"/-- d\n  {OTHER}\n  -/", TAG), (f"/-- d\n  {TAG}\n  -/", "replaced"))
        self.assertEqual(tag.with_tag("/-- d\n    -/", TAG), (f"/-- d\n    {TAG}\n    -/", "added"))

    def test_the_tag_goes_in_front_of_an_indented_command_like_it(self):
        self.assertEqual(tag.with_tag("/-- d -/", TAG, "  "), (f"/-- d\n  {TAG}\n  -/", "added"))

    def test_tag_on_the_closing_line_is_replaced(self):
        self.assertEqual(tag.with_tag(f"/-- d\n{OTHER}-/", TAG), (f"/-- d\n{TAG}-/", "replaced"))


class Law(unittest.TestCase):
    def test_tagged_text_is_equivalent_to_the_original(self):
        new, *_ = tag.tag_text(FIXTURE, items())
        self.assertTrue(tag.equivalent(FIXTURE, new))

    def test_strip_gives_back_the_code_exactly_and_the_docs_up_to_their_ends(self):
        new, *_ = tag.tag_text(FIXTURE, items())
        # only the whitespace in front of a docstring's closing may differ (`text -/` became `text\n-/`), and the fixture's old tag is gone from both
        ends = lambda s: re.sub(r"[ \t\n]*-/", "-/", s)  # noqa: E731
        self.assertEqual(ends(tag.strip_text(new)), ends(tag.strip_text(FIXTURE)))
        self.assertNotIn("@isnad", tag.strip_text(new))
        self.assertEqual(tag.strip_text(new).count("theorem"), FIXTURE.count("theorem"))

    def test_a_docstring_the_tagger_created_goes_whole(self):
        new, *_ = tag.tag_text(FIXTURE, items(["Fx.no_doc"]))
        self.assertEqual(tag.strip_text(new), tag.strip_text(FIXTURE))
        self.assertNotIn("/--\n@isnad", new.replace(f"/--\n{TAG}\n-/\ntheorem no_doc", ""))

    def test_an_empty_docstring_in_front_of_code_on_its_line_costs_no_code(self):
        # `/-- -/ theorem …`: nothing follows the docstring but a space, and the strip must not take a character of the code with it
        self.assertEqual(tag.strip_text("/-- -/ theorem t : True := trivial\n"), " theorem t : True := trivial\n")
        self.assertEqual(tag.strip_text("/-- -/"), "")
        self.assertEqual(tag.strip_text("  /-- -/\ntheorem t : True := trivial\n"), "  \ntheorem t : True := trivial\n")

    def test_changed_code_is_not_equivalent(self):
        new, *_ = tag.tag_text(FIXTURE, items())
        self.assertFalse(tag.equivalent(FIXTURE, new.replace("a + 0 = a", "a + 1 = a", 1)))

    def test_a_changed_docstring_word_is_not_equivalent(self):
        new, *_ = tag.tag_text(FIXTURE, items())
        self.assertFalse(tag.equivalent(FIXTURE, new.replace("many\nlines", "few\nlines", 1)))

    def test_a_dropped_theorem_is_not_equivalent(self):
        new, *_ = tag.tag_text(FIXTURE, items())
        self.assertFalse(tag.equivalent(FIXTURE, new.replace("theorem nested (a : Nat) : a = a := rfl\n", "")))

    def test_a_docstring_made_from_a_comment_is_not_equivalent(self):
        # `/-` and `/--` are different things to Lean: turning one into the other changes what attaches to the theorem
        new, *_ = tag.tag_text(FIXTURE, items())
        self.assertFalse(tag.equivalent(FIXTURE, new.replace("/-- one line", "/- one line", 1)))


class Skips(unittest.TestCase):
    def test_a_generated_twin_is_skipped_with_the_reason(self):
        v = RANGES["Fx.one_line"]
        twin = tag.Item("Fx.one_line_twin", tuple(v["range"]), tuple(RANGES["Fx.many_lines"]["sel"]), TAG)
        new, counts, skipped = tag.tag_text(FIXTURE, [twin])
        self.assertEqual(new, FIXTURE)
        self.assertEqual(len(skipped), 1)
        self.assertIn("generated", skipped[0][1])

    def test_two_theorems_at_one_command_are_both_skipped(self):
        v = RANGES["Fx.one_line"]
        a = tag.Item("Fx.one_line", tuple(v["range"]), tuple(v["sel"]), TAG)
        b = tag.Item("Fx.one_line", tuple(v["range"]), tuple(v["sel"]), OTHER)
        new, _, skipped = tag.tag_text(FIXTURE, [a, b])
        self.assertEqual(new, FIXTURE)
        self.assertEqual(len(skipped), 2)
        self.assertIn("several theorems", skipped[0][1])

    def test_crlf_files_are_skipped_whole(self):
        crlf = FIXTURE.replace("\n", "\r\n")
        new, counts, skipped = tag.tag_text(crlf, items())
        self.assertEqual(new, crlf)
        self.assertEqual(len(skipped), 12)
        self.assertEqual(sum(counts.values()), 0)
        self.assertIn("CRLF", skipped[0][1])

    def test_a_position_outside_the_file_is_skipped(self):
        it = tag.Item("Fx.x", (900, 0, 901, 1), (900, 0, 900, 1), TAG)
        new, _, skipped = tag.tag_text(FIXTURE, [it])
        self.assertEqual(new, FIXTURE)
        self.assertIn("outside the file", skipped[0][1])

    def test_an_unclosed_docstring_is_skipped(self):
        text = "/-- never closed\ntheorem t : True := trivial\n"
        it = tag.Item("t", (1, 0, 2, 33), (2, 8, 2, 9), TAG)
        new, _, skipped = tag.tag_text(text, [it])
        self.assertEqual(new, text)
        self.assertIn("never closed", skipped[0][1])

    def test_a_command_that_does_not_start_its_line_is_skipped(self):
        text = "namespace A theorem t : True := trivial\n"
        it = tag.Item("A.t", (1, 12, 1, 39), (1, 20, 1, 21), TAG)
        new, _, skipped = tag.tag_text(text, [it])
        self.assertEqual(new, text)
        self.assertIn("does not start its line", skipped[0][1])


class Scanning(unittest.TestCase):
    def kinds(self, text):
        return [k for k, *_ in tag.scan(text)]

    def test_a_docstring_inside_a_string_is_not_a_docstring(self):
        self.assertEqual(self.kinds('def s := "/-- not a doc -/"\n'), ["code", "string", "code"])

    def test_a_docstring_inside_a_comment_is_not_a_docstring(self):
        self.assertEqual(self.kinds("-- /-- not a doc -/\ntheorem t : True := trivial\n"), ["comment", "code"])
        self.assertEqual(self.kinds("/- /-- not a doc -/ -/\ntheorem t : True := trivial\n"), ["comment", "code"])

    def test_module_doc_is_a_comment_not_a_docstring(self):
        self.assertEqual(self.kinds("/-! module doc -/\ntheorem t : True := trivial\n"), ["comment", "code"])

    def test_the_empty_comment_is_not_a_docstring(self):
        self.assertEqual(self.kinds("/--/\ntheorem t : True := trivial\n"), ["comment", "code"])

    def test_every_byte_is_in_exactly_one_segment(self):
        segs = tag.scan(FIXTURE)
        self.assertEqual(segs[0][1], 0)
        self.assertEqual(segs[-1][2], len(FIXTURE))
        for (_, _, e), (_, s, _) in zip(segs, segs[1:], strict=False):
            self.assertEqual(e, s)

    def test_an_escaped_quote_does_not_end_a_string(self):
        self.assertEqual(self.kinds('def s := "a\\"b /-- c -/"\n'), ["code", "string", "code"])

    def test_a_comment_that_is_never_closed_runs_to_the_end(self):
        self.assertEqual(tag.skip_block_comment("/- a /- b -/ c", 0), len("/- a /- b -/ c"))


def position(text, off):
    line_start = text.rfind("\n", 0, off) + 1
    return text.count("\n", 0, off) + 1, off - line_start


def ranges_of(text, n):
    """What Lean would say for the generated file: the command of `theorem tK` starts at its docstring, else its attribute line, else the keyword."""
    segs = tag.scan(text)
    out = []
    for k in range(n):
        kw = text.index(f"theorem t{k} ")
        name = kw + len("theorem ")
        start = kw
        # an attribute on the line before, or in front of the keyword on its line
        line = text.rfind("\n", 0, kw) + 1
        if text[line:kw].strip().startswith("@["):
            start = line + (len(text[line:kw]) - len(text[line:kw].lstrip()))
        elif text[:line].rstrip().endswith("]") and text[:line].rstrip().rsplit("\n", 1)[-1].strip().startswith("@["):
            above = text[:line].rstrip().rsplit("\n", 1)[-1]
            start = text.rindex(above, 0, line)
            start += len(above) - len(above.lstrip())
        for kind, a, b in segs:
            if kind == "doc" and b <= start and not text[b:start].strip():
                start = a
        end = text.index("\n", kw)
        out.append(tag.Item(f"t{k}", (*position(text, start), *position(text, end)), (*position(text, name), *position(text, name + len(f"t{k}"))), TAG))
    return out


class Fuzz(unittest.TestCase):
    """Docstring shapes nobody wrote on purpose: the tagger must tag, replace and strip every one of them without touching anything else."""

    DOCS = [
        None,
        "/-- one -/",
        "/-- one\n-/",
        "/--\n  many\n  lines\n  -/",
        "/-- has /- nested -/ comment -/",
        "/-- has -- dashes and \"quotes\" -/",
        "/-- -/",
        "/--\n-/",
        f"/-- old\n{OTHER}\n-/",
        f"/-- old\n{OTHER}-/",
        f"/-- old\n  {OTHER}\n  -/",
        f"/--\n{OTHER}\n-/",
        f"/-- {TAG}-/",
        "/-- trailing spaces   \n-/",
        "/-- ünïcode ⊢ ∀ -/",
    ]
    ATTRS = ["", "@[simp]\n", "@[simp] ", "@[simp, norm_cast]\n"]

    def build(self, rnd, n):
        parts = ["import Lean\n"]
        for k in range(n):
            indent = rnd.choice(["", "", "  "])
            doc, attr = rnd.choice(self.DOCS), rnd.choice(self.ATTRS)
            head = f"{indent}{doc}\n" if doc else ""
            parts.append(f"\n{head}{indent}{attr}theorem t{k} : True := trivial\n")
        return "".join(parts)

    def test_random_files(self):
        import random

        rnd = random.Random(20261005)
        for trial in range(300):
            n = rnd.randint(1, 6)
            text = self.build(rnd, n)
            with self.subTest(trial=trial):
                new, counts, skipped = tag.tag_text(text, ranges_of(text, n))
                self.assertEqual(skipped, [], text)
                self.assertEqual(new.count("@isnad1 "), n, new)
                self.assertTrue(tag.equivalent(text, new), (text, new))
                self.assertTrue(all(new[b - 2 : b] == "-/" for kind, _, b in tag.scan(new) if kind == "doc"), new)  # every docstring is closed
                # tagging again with the same tag changes nothing; with another tag it replaces and never duplicates
                same, counts2, skipped2 = tag.tag_text(new, ranges_of(new, n))
                self.assertEqual((same, skipped2), (new, []), new)
                self.assertEqual(counts2["same"], n)
                other = [tag.Item(i.name, i.rng, i.sel, OTHER) for i in ranges_of(new, n)]
                swapped, counts3, _ = tag.tag_text(new, other)
                self.assertEqual(swapped.count("@isnad1 "), n)
                self.assertEqual(swapped.count(TAG), 0)
                self.assertEqual(counts3["replaced"], n)
                self.assertTrue(tag.equivalent(text, swapped))
                # taking the tags out leaves the original (up to the whitespace before a docstring's closing)
                gone = tag.strip_text(new)
                self.assertNotIn("@isnad", gone)
                self.assertTrue(tag.equivalent(tag.strip_text(text), gone))
                self.assertEqual(gone.count("theorem"), n)


if __name__ == "__main__":
    unittest.main()
