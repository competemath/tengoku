# Campaign gate: a change to the pipeline comes with a campaign, or with the approver's waiver

The pipeline (the PR gate, the merge queue, the scripts they run) is tested by the scenario campaign in a sandbox copy of this repository (`scripts/ci/campaign/`, [`testing.md`](testing.md)).
A change to the pipeline that skips the campaign is how a gate change reaches `main` untested. `campaign-gate` (`.github/workflows/campaign-gate.yml`, `scripts/ci/campaign_check.py`) makes
that mechanical: it decides from the files whether a PR is CI-class and, if it is, fails until the PR has a campaign or a waiver.

## What is CI-class (decided by `scripts/ci/ci_paths.py`, not by anyone's judgement)

| Path | Why |
|---|---|
| anything under `scripts/ci/`, anything under `.github/workflows/`, `.github/CODEOWNERS` | the gate and the queue themselves |
| `schemas/` (except `schemas/sources.json`), `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `tools/*.lean` | data the gates read to decide what they accept (`allowed-options.json`, `command-keywords.json`, the toolchain a bundle is checked against). `schemas/sources.json` is the registry itself: it grows with every registry PR and the append-only rule judges it |
| any other script (`.py`, `.sh`, `.mjs`) that a workflow or a `scripts/ci/` entry point reaches | a gate dependency. The closure follows Python imports (also imports inside functions: `roots_check.py` imports `roots_tree.py` late) and `scripts/...` paths named in a script or a workflow, to a fixed point |
| `*.md` | exempt (documentation) |

The case that made this rule: `scripts/roots_tree.py` is not under `scripts/ci/`, yet the roots gate runs it, so a change to it changes what the gate accepts. The closure catches it
(`test_roots_tree_is_a_gate_dependency_in_the_real_tree` runs against this repository's real files). The closure is deliberately broad: a script a gate imports, even for one helper, is CI-class;
the cost is a waiver for a change that does not touch gate behaviour, the benefit is no silent path.

## What satisfies the check

1. **A campaign for the head commit.** Not available yet (see "Not built"). `emissary-sandbox` has this (`campaign.yml` plus an attested result); `tengoku-sandbox` does not.
2. **A waiver**: a review of the PR, **on the head commit**, by the approver account (the constant `APPROVER` in `scripts/ci/campaign_check.py`, `mikaelbashir14096545`; a constant on purpose, a repository variable could be changed by an admin with no pull request to see it), in state APPROVED or COMMENTED (a DISMISSED or CHANGES_REQUESTED review does not count), whose body has a line

   `campaign-waiver: <reason, at least 20 characters>`

   The waiver binds to the account because the agent that opens these PRs works as another account and cannot write that review; a label or an author's comment would not bind it.
   It binds to the commit because a review is on one commit: any push voids it, like an approval. A review written after the check ran takes effect when the check is re-run (the script reads the reviews
   when it runs); `pull_request_review` is not a trigger, because a workflow triggered by it would run the PR's copy of the file.

The check always runs on every PR to `main` (so it can be required) and passes at once when nothing is CI-class. On the merge queue entry it reports success: the PR was judged.

## Why a PR cannot weaken it

`pull_request_target`: the workflow and the script run as they are on `main`; nothing of the PR is checked out or run; the file list and the reviews come from the API. A change to the gate itself takes
effect once merged, which is why this very PR is CI-class and needs the same waiver (or a campaign) as any other.

## Not built, and not decided here

- **The per-commit campaign for tengoku** (a `tengoku-sandbox` workflow that runs the scenarios for a commit and attests the result, verified here as `emissary-archangel`'s `campaign-gate.yml` does). Until it exists
  the waiver is the only way through, so every CI-class PR needs the approver's explicit review. That is intended: the campaign is run by hand today (`scripts/ci/campaign/README.md`), and the waiver says so on record.
- **Making `campaign-gate` a required check** is a ruleset setting of the repository (owner), not a workflow. Until it is required the check reports and blocks nothing.
- The closure is a static approximation: a script run through a path built at run time, or loaded by a mechanism other than import and the quoted `scripts/...` path, is not seen. A real campaign remains the proof.

## Tests

`scripts/ci/tests/test_campaign_check.py`: paths, the closure (including the real case), and the waiver (wrong author, old commit, short reason, case of the account name, newest acceptable review wins,
an approval without the line is not a waiver). Mutants checked by hand: closure off, commit binding off, approver check off, reason length off each fail at least one test.
