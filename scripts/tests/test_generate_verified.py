"""generate.py's verified generator: the tree is built from the records' verified contexts, never the corpus.
Checks the modules it writes (Lean is not run: the merge queue builds them)."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from generate import prelude_blocks, topo_order  # noqa: E402

HEAD = "set_option linter.all false -- [Emissary] lints are not drift; the kernel decides\n\n"


def prelude(mod: str, body: str, kind: str = "verbatim") -> str:
    return f"-- [Emissary prelude] {mod} — {kind} (imports stripped)\n{body}\n"


def own(path: str, line: int, body: str) -> str:
    return f"-- [Emissary] {path}, everything before line {line} (imports stripped; sibling theorems the target does not use omitted)\n{body}\n"


def rec(name: str, src: str, context: str, stmt: str | None = None) -> dict:
    return {
        "name": name,
        "statement": stmt or f"theorem {name} : True",
        "proof": ":= trivial",
        "context": context,
        "source_path": src,
        "status": "trusted",
        "promoted_at": "2026-01-01T00:00:00Z",
        "library": "lib-x",
        "source_url": f"https://example.com/{src}",
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
    }


class Parsing(unittest.TestCase):
    def test_prelude_blocks_run_to_the_next_marker_or_the_own_file_marker(self):
        ctx = HEAD + prelude("Lx.A", "def a := 1") + prelude("Lx.B", "def b := a", "expanded") + own("Lx/C.lean", 9, "def c := b")
        blocks = prelude_blocks(ctx)
        self.assertEqual([m for m, _ in blocks], ["Lx.A", "Lx.B"])
        self.assertEqual(blocks[1][1].strip(), "def b := a")  # an expanded block counts too (the legacy generator missed it)
        self.assertNotIn("def c", blocks[1][1])

    def test_topo_order_respects_every_context(self):
        self.assertEqual(topo_order([["A", "B", "D"], ["C", "D"], ["B", "C"]]), ["A", "B", "C", "D"])


class Generate(unittest.TestCase):
    def setUp(self):
        self.out = Path(tempfile.mkdtemp())
        shutil.copytree(ROOT / "scripts", self.out / "scripts")
        (self.out / "schemas").mkdir()
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps({"corpora": {"lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"]}}})
        )
        (self.out / "Tengoku").mkdir()
        (self.out / "data" / "trusted").mkdir(parents=True)

    def tearDown(self):
        shutil.rmtree(self.out)

    def generate(self, records: list[dict]) -> str:
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text("".join(json.dumps(r) + "\n" for r in records))
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", "/nonexistent", "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        return r.stdout

    def read(self, rel: str) -> str:
        return (self.out / "Tengoku" / rel).read_text()

    def test_deps_are_the_verified_blocks_and_nothing_from_outside_the_tree(self):
        a = prelude("Lx.A", "import Architect\n@[blueprint] def a := 1")  # what a block could never hold: the bridge strips it
        ctx1 = HEAD + prelude("Lx.A", "def a := 1") + prelude("Lx.B", "def b := a") + own("Lx/C.lean", 9, "namespace Lx\ndef c := b")
        ctx2 = HEAD + prelude("Lx.A", "def a := 1") + own("Lx/D.lean", 3, "")
        self.generate([rec("Lx.t1", "Lx/C.lean", ctx1), rec("t2", "Lx/D.lean", ctx2)])
        dep_a, dep_b = self.read("LibX/Deps/A.lean"), self.read("LibX/Deps/B.lean")
        self.assertIn("def a := 1", dep_a)
        self.assertIn("import Tengoku\n", dep_a)
        self.assertNotIn("Deps.B", dep_a)
        self.assertIn("import Tengoku.LibX.Deps.A", dep_b)  # the block before it in the context
        c = self.read("LibX/C.lean")
        self.assertIn("import Tengoku\nimport Tengoku.LibX.Deps.A\nimport Tengoku.LibX.Deps.B", c)
        self.assertIn("def c := b", c)
        self.assertIn("theorem Lx.t1 : True", c)
        self.assertIn("end Lx", c)  # the own-file prefix left the namespace open
        self.assertNotIn("namespace LibX", c)  # never wrapped: the text is exactly what was verified
        for f in (self.out / "Tengoku").rglob("*.lean"):
            self.assertNotIn("Architect", f.read_text(), f)
        self.assertIn("import Tengoku.LibX", self.read("All.lean"))
        del a

    def test_the_most_common_block_version_wins(self):
        v1 = HEAD + prelude("Lx.A", "def a := 1") + own("Lx/C.lean", 2, "")
        v2 = HEAD + prelude("Lx.A", "def a := 2") + own("Lx/C.lean", 2, "")
        self.generate([rec("t1", "Lx/C.lean", v1), rec("t2", "Lx/C.lean", v1), rec("t3", "Lx/C.lean", v2)])
        dep = self.read("LibX/Deps/A.lean")
        self.assertIn("def a := 1", dep)
        self.assertIn("2 versions across records", dep)

    def test_a_theorem_a_deps_module_already_has_is_not_declared_again(self):
        # Lx/A.lean is another record's prelude; its own record (t_a, the original text) lives in Deps/A already
        ctx_b = HEAD + prelude("Lx.A", "def a := 1\ntheorem t_a : True := trivial") + own("Lx/B.lean", 4, "")
        ctx_a = HEAD + own("Lx/A.lean", 2, "def a := 1")
        self.generate([rec("t_b", "Lx/B.lean", ctx_b), rec("t_a", "Lx/A.lean", ctx_a)])
        a_mod = self.read("LibX/A.lean")
        self.assertNotIn("theorem t_a", a_mod)
        self.assertNotIn("def a := 1", a_mod)
        self.assertIn("import Tengoku.LibX.Deps.A", a_mod)  # its own Deps module
        self.assertIn("theorem t_b", self.read("LibX/B.lean"))

    def test_legacy_libraries_are_untouched_by_the_verified_path(self):
        (self.out / "schemas" / "sources.json").write_text(
            json.dumps({"corpora": {"lib-x": {"repo": "r", "commit": "c", "roots": ["Lx"], "generator": "legacy"}}})
        )
        corpus = self.out / "corpus"
        (corpus / "Lx").mkdir(parents=True)
        (corpus / "Lx" / "A.lean").write_text("def a := 1\n")
        ctx = HEAD + prelude("Lx.A", "def a := 1") + own("Lx/C.lean", 2, "")
        (self.out / "data" / "trusted" / "lib-x.jsonl").write_text(json.dumps(rec("t1", "Lx/C.lean", ctx)) + "\n")
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", str(corpus), "--libraries", "lib-x"],
            cwd=self.out,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("namespace LibX", self.read("LibX/Deps/A.lean"))  # the legacy generator wraps; the verified one never does


if __name__ == "__main__":
    unittest.main()
