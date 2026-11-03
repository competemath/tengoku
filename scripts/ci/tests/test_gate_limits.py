"""The time limits of the pr-gate jobs that read a blobless clone of main.

3 Nov 2026: with four more libraries in main, `actions/checkout` (full history, blobless, then main's whole tree) and `every import resolves` (one blob fetched per module of an
intake PR) took longer than the 5 and 10 minutes the jobs were given; on the three intake PRs of that evening (#698, #699, #702) one job or another was cancelled at its limit
in 12 of 15 attempts, and the PR stayed red with every check it was waiting for passing on the next. A job that checks a PR out the way pr-gate does has room for it.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

import yaml

TREE = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(TREE / "scripts" / "ci"))

CHECKOUT_MINUTES = 15  # the least a job that checks out main's tree blobless may be given
IMPORTS_MINUTES = 30  # `every import resolves` reads one blob per module of the PR


class GateLimits(unittest.TestCase):
    @staticmethod
    def jobs():
        doc = yaml.safe_load((TREE / ".github" / "workflows" / "pr-gate.yml").read_text(encoding="utf-8"))
        return doc["jobs"]

    @staticmethod
    def blobless(job):
        return any(
            'filter: "blob:none"' in str(step.get("with", {})) or "blob:none" in str(step.get("with", {})) for step in job.get("steps", [])
        )

    def test_every_job_that_checks_out_blobless_has_at_least_fifteen_minutes(self):
        short = {
            name: job.get("timeout-minutes")
            for name, job in self.jobs().items()
            if self.blobless(job) and (job.get("timeout-minutes") or 0) < CHECKOUT_MINUTES
        }
        self.assertEqual(short, {})

    def test_the_import_check_has_at_least_thirty_minutes(self):
        self.assertGreaterEqual(self.jobs()["imports"]["timeout-minutes"], IMPORTS_MINUTES)

    def test_the_jobs_that_check_out_blobless_are_found(self):
        # the test above must not pass by finding nothing
        self.assertGreaterEqual(sum(1 for job in self.jobs().values() if self.blobless(job)), 8)


if __name__ == "__main__":
    unittest.main()
