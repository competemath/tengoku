"""promotion_notify.py: each contributor PR hears which of its records a promotion made trusted."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_gates import GOOD, Repo  # noqa: E402


def rec(name: str, tier: str = "staging") -> str:
    r = {**GOOD, "name": name, "statement": f"theorem {name} : 1 + 1 = 2", "status": tier}
    if tier == "trusted":
        r["promoted_at"] = "2026-09-29T00:00:00Z"
    return json.dumps(r) + "\n"


class PromotionNotify(unittest.TestCase):
    def test_each_pr_hears_about_its_own_records(self):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write("data/staging/lib/pr-12.jsonl", rec("Lib.a") + rec("Lib.b"))
        r.commit("Stage lib: 2 records (#12)")
        r.append("data/staging/lib.jsonl", rec("Lib.c"))
        r.commit("Stage lib: 1 record (#13)")
        # the promotion: the three records go to trusted, the per-PR file goes, Lib.c leaves the flat file
        r.append("data/trusted/lib.jsonl", rec("Lib.a", "trusted") + rec("Lib.b", "trusted") + rec("Lib.c", "trusted"))
        (r.dir / "data/staging/lib/pr-12.jsonl").unlink()
        flat = (r.dir / "data/staging/lib.jsonl").read_text().splitlines(keepends=True)
        (r.dir / "data/staging/lib.jsonl").write_text("".join(x for x in flat if '"Lib.c"' not in x))
        r.commit("Promote: 3 records (#20)")
        rc, out = r.gate("promotion_notify.py", "HEAD~1", "HEAD", "20", env={"TENGOKU_COMMENT_DRY": "1"})
        self.assertEqual(rc, 0, out)
        self.assertIn("would comment on #12", out)
        self.assertIn("**2 of the records this PR added are now trusted** (promotion #20): `Lib.a`, `Lib.b`", out)
        self.assertIn("would comment on #13", out)
        self.assertIn("**1 of the records this PR added is now trusted**", out)
        self.assertNotIn("#20:", out)

    def test_a_commit_without_a_pr_is_not_told(self):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.append("data/trusted/lib.jsonl", rec("Lib.z", "trusted"))
        r.commit("direct push")
        rc, out = r.gate("promotion_notify.py", "HEAD~1", "HEAD", "21", env={"TENGOKU_COMMENT_DRY": "1"})
        self.assertEqual(rc, 0, out)
        self.assertIn("no contributor PR to tell", out)


if __name__ == "__main__":
    unittest.main()
