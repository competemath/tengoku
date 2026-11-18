"""requeue_lost.py: a PR whose merge-queue build lost its runner goes back into the queue by itself.

Real cases (tengoku, 17 and 18 Nov 2026): six queue builds ended with "The hosted runner lost communication with the server", each with NO failing step,
each after 60 to 120 minutes: #885 (queue-gate run 44110156039, 120 min), #897 (74 min), #894 (124 min), #907 (65 and 61 min), #910 (81 min). The PRs were clean (their
gates had passed) and were put back by hand. The merge-group branch names, the annotation text and the shape of the jobs are those of the real runs.

Invariants: a one-PR group is recognised by its branch and nothing else is; a lost runner is a failed queue-build job with no failing step AND the annotation; a real
failure (a failing step, even with the annotation text) is never re-queued; a PR that is closed, labelled ejected, or already removed more than MAX_REMOVALS times is left
alone; the re-queue is `gh pr merge --auto` with the bot's token, never the job's, and only once the queue no longer holds the entry; without the token nothing is
changed. Mutants (each must fail a check): re-queueing a failure that has a failing step; ignoring the removal cap; using the job's token for the merge.
"""

from __future__ import annotations

import inspect
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import requeue_lost as rl  # noqa: E402

REPO = "competemath/tengoku"
REAL_ANNOTATION = {
    "annotation_level": "failure",
    "message": "The hosted runner lost communication with the server. Anything in your workflow that terminates the runner process, starves it for CPU/Memory, or blocks its network access can cause this error.",
}
NOTICE = {"annotation_level": "notice", "message": "The ubuntu-latest label will migrate to Ubuntu 26 beginning October 19, 2026."}
STEPS_OK = [{"conclusion": "success"}] * 20 + [
    {"conclusion": "cancelled"},
    {"conclusion": "skipped"},
]  # as the real job: nothing failed, the job just ended
BRANCHES = {
    885: "gh-readonly-queue/main/pr-885-ea0f51fcc6e0bb3f3d0e5a3b0b2c0c9e2d8f7a61",
    910: "gh-readonly-queue/main/pr-910-bb7797b81ac03d72721e86e38f8a717e02ef94a1",
}


class Fake:
    """gh, by what it is asked: the jobs of the run, the annotations, the PR, its timeline, the queue entry, and what is written"""

    def __init__(self, job=None, notes=None, state="OPEN", labels=(), removals=1, entries=(None,)):
        self.job = job if job is not None else {"id": 77, "name": "queue-build", "conclusion": "failure", "steps": STEPS_OK}
        self.notes = notes if notes is not None else [NOTICE, REAL_ANNOTATION]
        self.state, self.labels, self.removals = state, labels, removals
        self.entries = list(entries)  # the answers to "is the PR in the queue?", one per look; the last repeats
        self.writes = []  # (arguments, token)
        self.sleeps = 0

    def gh(self, args, token=None):
        a = " ".join(args)
        if "/jobs" in a:
            return json.dumps([self.job, {"id": 78, "name": "queue-gate", "conclusion": "failure", "steps": []}])
        if "/annotations" in a:
            return json.dumps(self.notes)
        if args[:2] == ["pr", "view"]:
            return json.dumps({"state": self.state, "labels": [{"name": x} for x in self.labels]})
        if "/timeline" in a:
            return "\n".join(["2026-11-18T05:42:38Z"] * self.removals)
        if args[:2] == ["api", "graphql"]:
            e = self.entries.pop(0) if len(self.entries) > 1 else self.entries[0]
            return json.dumps({"data": {"repository": {"pullRequest": {"mergeQueueEntry": e}}}})
        self.writes.append((args, token))
        return ""

    def run(self, branch=BRANCHES[910], token="bot-token", repo=REPO):
        said = []
        rc = rl.main(
            "44110156039", branch, repo, token, gh=self.gh, sleep=lambda s: setattr(self, "sleeps", self.sleeps + 1), say=said.append
        )
        return rc, said

    def merges(self):
        return [(a, t) for a, t in self.writes if a[:2] == ["pr", "merge"]]


class Branch(unittest.TestCase):
    def test_the_real_group_branches(self):
        for pr, b in BRANCHES.items():
            self.assertEqual(rl.group_pr(b), pr)

    def test_nothing_else_is_a_group(self):
        for b in (
            "main",
            "intake/dandelin-1-part-001",
            "gh-readonly-queue/main/pr-910",
            "gh-readonly-queue/main/pr-910-xyz",
            "x/gh-readonly-queue/main/pr-1-abcdef0",
            "gh-readonly-queue/main/pr-1-abcdef0/../x",
            "",
        ):
            self.assertIsNone(rl.group_pr(b), b)


class LostRunner(unittest.TestCase):
    def test_the_real_job_is_a_lost_runner(self):
        self.assertTrue(rl.lost_runner(Fake().job, Fake().notes))

    def test_a_failing_step_is_never_a_lost_runner_even_with_the_text(self):
        job = {"conclusion": "failure", "steps": STEPS_OK + [{"conclusion": "failure"}]}
        self.assertFalse(rl.lost_runner(job, [REAL_ANNOTATION]))

    def test_no_annotation_no_lost_runner(self):
        self.assertFalse(rl.lost_runner(Fake().job, [NOTICE]))
        self.assertFalse(rl.lost_runner(Fake().job, []))

    def test_a_job_that_did_not_fail_is_not(self):
        self.assertFalse(rl.lost_runner({"conclusion": "cancelled", "steps": []}, [REAL_ANNOTATION]))
        self.assertFalse(rl.lost_runner({"conclusion": "success", "steps": []}, [REAL_ANNOTATION]))

    def test_a_notice_with_the_words_is_not_a_failure_annotation(self):
        self.assertFalse(rl.lost_runner(Fake().job, [{"annotation_level": "notice", "message": REAL_ANNOTATION["message"]}]))


class Requeue(unittest.TestCase):
    def test_the_real_case_goes_back_with_the_bots_token_once_the_queue_let_go(self):
        f = Fake(entries=({"id": "E"}, {"id": "E"}, None))
        rc, said = f.run()
        self.assertEqual(rc, 0)
        self.assertEqual(f.sleeps, 2)
        self.assertEqual(f.merges(), [(["pr", "merge", "910", "-R", REPO, "--auto"], "bot-token")])
        self.assertTrue(any(a[:2] == ["pr", "comment"] and t == "bot-token" for a, t in f.writes))
        self.assertIn("re-queued", said[-1])

    def test_a_real_failure_is_left_to_queue_comment(self):
        f = Fake(job={"id": 77, "name": "queue-build", "conclusion": "failure", "steps": STEPS_OK + [{"conclusion": "failure"}]})
        f.run()
        self.assertEqual(f.writes, [])

    def test_closed_or_ejected_is_left_alone(self):
        for kw in ({"state": "CLOSED"}, {"state": "MERGED"}, {"labels": ["ejected"]}):
            f = Fake(**kw)
            f.run()
            self.assertEqual(f.writes, [], kw)

    def test_the_fifth_removal_is_left_to_a_person(self):
        f = Fake(removals=rl.MAX_REMOVALS + 1)
        f.run()
        self.assertEqual(f.writes, [])
        f = Fake(removals=rl.MAX_REMOVALS)
        f.run()
        self.assertEqual(len(f.merges()), 1)

    def test_still_in_the_queue_after_the_wait_does_nothing(self):
        f = Fake(entries=({"id": "E"},))
        f.run()
        self.assertEqual(f.writes, [])
        self.assertEqual(f.sleeps, rl.WAIT_TRIES)

    def test_without_the_bots_token_nothing_changes(self):
        f = Fake()
        rc, said = f.run(token="")
        self.assertEqual((rc, f.writes), (0, []))
        self.assertIn("NOT re-queued", said[-1])

    def test_not_a_one_pr_group_or_a_bad_run_id(self):
        f = Fake()
        f.run(branch="main")
        self.assertEqual(f.writes, [])
        said = []
        self.assertEqual(rl.main("1; rm -rf /", BRANCHES[910], REPO, "t", gh=f.gh, say=said.append), 0)
        self.assertEqual(f.writes, [])

    def test_every_real_case_group_is_recognised(self):
        for b in (
            "gh-readonly-queue/main/pr-897-8a628b99838e8e19adcab5c881da57" + "0123456",
            "gh-readonly-queue/main/pr-907-f1a829d03b1e09b1096bab0d0439c056ac8e82b4",
        ):
            self.assertIsNotNone(rl.group_pr(b))

    def test_mutant_a_failing_step_is_requeued(self):
        src = inspect.getsource(rl.lost_runner).replace(
            "return False  # a step failed: a real failure, explained by queue_comment.py", "pass"
        )
        ns = dict(vars(rl))
        exec(src, ns)
        job = {"conclusion": "failure", "steps": STEPS_OK + [{"conclusion": "failure"}]}
        self.assertTrue(ns["lost_runner"](job, [REAL_ANNOTATION]))  # the mutant re-queues a real failure; the real function refuses it
        self.assertFalse(rl.lost_runner(job, [REAL_ANNOTATION]))

    def test_mutant_no_removal_cap(self):
        src = inspect.getsource(rl.main)
        old = "if removals > MAX_REMOVALS:"
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(rl))
        exec(src.replace(old, "if False:"), ns)
        f = Fake(removals=rl.MAX_REMOVALS + 3)
        ns["main"]("1", BRANCHES[910], REPO, "t", gh=f.gh, sleep=lambda s: None, say=lambda s: None)
        self.assertEqual(len(f.merges()), 1)  # the mutant re-queues forever; the real main stops at the cap (test above)

    def test_the_merge_never_uses_the_jobs_token(self):
        src = inspect.getsource(rl.main)
        self.assertIn('gh(["pr", "merge", str(pr), "-R", repo, "--auto"], bot_token)', src)


if __name__ == "__main__":
    unittest.main()
