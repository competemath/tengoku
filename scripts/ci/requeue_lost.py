#!/usr/bin/env python3
"""requeue_lost.py <queue-gate run id> <merge-group branch> — put a PR back into the merge queue when its build lost its runner.

A merge-queue build (queue-gate's `queue-build` job) can end when GitHub's hosted runner loses contact with the server ("The hosted runner lost
communication with the server"): the job fails with NO failing step, no Lean error is read, `queue_comment.py` has no facts to explain, and the PR is
dropped from the queue with nothing for its author to fix. The part is clean; only the build was lost. Six queue builds ended this way on
17 and 18 Nov 2026 (tengoku#885, #897, #894, #907 twice, #910), each after 60 to 120 minutes, each put back by hand.

This runs from `requeue-lost.yml` (a workflow_run of queue-gate, main's copy). The facts about the failed run come from the API and are data. It
re-queues only when ALL of this holds: the group is one PR's (`gh-readonly-queue/main/pr-N-<sha>`), the `queue-build` job failed with no failing
step AND its annotation says the runner lost communication, the PR is open and not labelled `ejected` (a real failure is explained and labelled by
`queue_comment.py`), and the queue has removed it at most MAX_REMOVALS times (a build that keeps dying is for a person). The re-queue is
`gh pr merge --auto` with the bot's token, as `rearm.yml` does: an entry the job token starts does not start the queue's own workflows."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time

GROUP = re.compile(r"gh-readonly-queue/[\w.-]+/pr-(\d{1,9})-[0-9a-f]{7,40}")
LOST = "lost communication with the server"
MAX_REMOVALS = 4  # removals by the queue, in all: the fifth is left to a person
WAIT_SECONDS = 20
WAIT_TRIES = 15  # five minutes for the queue to take the entry out before the re-queue


def group_pr(branch: str) -> int | None:
    """the PR a merge-group branch is built for, or None"""
    m = GROUP.fullmatch(branch)
    return int(m.group(1)) if m else None


def lost_runner(job: dict, annotations: list[dict]) -> bool:
    """the build job failed with no failing step, and GitHub says the runner was lost"""
    if job.get("conclusion") != "failure":
        return False
    if any(s.get("conclusion") == "failure" for s in job.get("steps") or []):
        return False  # a step failed: a real failure, explained by queue_comment.py
    return any(a.get("annotation_level") == "failure" and LOST in (a.get("message") or "") for a in annotations)


def sh(args: list[str], token: str | None = None) -> str:
    env = {**os.environ, **({"GH_TOKEN": token} if token else {})}
    r = subprocess.run(["gh", *args], capture_output=True, text=True, env=env)
    if r.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args[:3])} failed: {r.stderr.strip()[:200]}")
    return r.stdout


def main(run_id: str, branch: str, repo: str, bot_token: str, gh=sh, sleep=time.sleep, say=print) -> int:
    pr = group_pr(branch)
    if pr is None or not re.fullmatch(r"\d{1,15}", run_id):
        say(f"not a one-PR merge group: {branch!r}")
        return 0
    jobs = json.loads(gh(["api", f"repos/{repo}/actions/runs/{run_id}/jobs", "--jq", ".jobs"]))
    build = [j for j in jobs if j.get("name") == "queue-build"]
    if len(build) != 1:
        say("no single queue-build job in this run")
        return 0
    notes = json.loads(gh(["api", f"repos/{repo}/check-runs/{build[0]['id']}/annotations"]))
    if not lost_runner(build[0], notes):
        say(f"#{pr}: the build did not lose its runner; its failure is explained on the PR")
        return 0
    info = json.loads(gh(["pr", "view", str(pr), "-R", repo, "--json", "state,labels"]))
    if info["state"] != "OPEN" or "ejected" in [x["name"] for x in info["labels"]]:
        say(f"#{pr}: not open, or labelled ejected: left alone")
        return 0
    removals = len(
        [
            x
            for x in gh(
                [
                    "api",
                    "--paginate",
                    f"repos/{repo}/issues/{pr}/timeline",
                    "--jq",
                    '.[] | select(.event == "removed_from_merge_queue") | .created_at',
                ]
            ).split()
            if x
        ]
    )
    if removals > MAX_REMOVALS:
        say(f"#{pr}: the queue has removed it {removals} times; left to a person")
        return 0
    owner, name = repo.split("/")
    query = f'{{repository(owner:"{owner}",name:"{name}"){{pullRequest(number:{pr}){{mergeQueueEntry{{id}}}}}}}}'
    for _ in range(WAIT_TRIES):  # the queue takes the entry out a moment after the verdict
        entry = json.loads(gh(["api", "graphql", "-f", f"query={query}"]))["data"]["repository"]["pullRequest"]["mergeQueueEntry"]
        if entry is None:
            break
        sleep(WAIT_SECONDS)
    else:
        say(f"#{pr}: still in the queue after the wait; nothing to do")
        return 0
    if not bot_token:
        say(f"#{pr}: lost its runner ({removals} removals); no TENGOKU_BOT_TOKEN, so it is NOT re-queued (press Merge when ready)")
        return 0
    gh(["pr", "merge", str(pr), "-R", repo, "--auto"], bot_token)
    body = (
        f"**Back in the merge queue — the build lost its runner, not your change.** GitHub's hosted runner lost contact with the server during this PR's "
        f"queue build (run {run_id}), so nothing was compiled or judged. It is queued again by itself (removal {removals} of {MAX_REMOVALS} allowed)."
    )
    gh(["pr", "comment", str(pr), "-R", repo, "--body", body], bot_token)
    say(f"#{pr}: re-queued after a lost runner (removal {removals})")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2], os.environ["GITHUB_REPOSITORY"], os.environ.get("BOT_TOKEN", "")))
