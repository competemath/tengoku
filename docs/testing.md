# How Tengoku is tested

Tengoku's promise is one sentence: **a trusted theorem is in the tree, and the
tree builds on the pinned toolchain with no errors, no `sorry`, and no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.** Everything below exists
to keep that sentence true for every change from anyone, without a human in
the loop for the common case, and to say clearly what went wrong when it is
not true.

There are five layers. Each one is cheap enough to run where it runs, and each
catches something the others cannot.

| Layer | Where | Runs on | Catches | Typical time |
|---|---|---|---|---|
| Unit tests of the gate scripts | `scripts/ci/tests/test_gates.py`, `scripts/tests/` | your machine, CI (`tooling-tests`) | a gate script that does not do what it claims | 5 s |
| Pre-commit hooks | `.pre-commit-config.yaml` | your machine, CI (`lint-python`) | lint, formatting, secrets, banked content — the same list in both places | seconds |
| The PR gate | `.github/workflows/pr-gate.yml` | every pull request | wrong shape of change: two purposes, edits to append-only data, forbidden constructs, missing credits, secrets, missing sign-off, unmet dependencies | 2–3 min |
| The merge queue | `.github/workflows/queue-gate.yml` | every merge group | wrong mathematics: a proof that does not compile, a `sorry`, a non-standard axiom, a hand-edited generated file | 3–7 min |
| The scenario campaign | `scripts/ci/campaign/` | a sandbox copy of the repo, on demand | a check that passes when it should fail — the tests of the tests | ~3 h for everything |

The nightly cache build (`.github/workflows/build.yml`) is not a test but the
queue depends on it: it compiles the tree once a day, publishes the result as
a release, and signs every part with a build-provenance attestation that the
queue verifies before unpacking.

## 1. The PR gate

Runs on `pull_request` (and on merge groups, where it repeats the cheap
checks). No Lean runs here; the whole thing is done in about three minutes.
The jobs, in the order they matter:

- **classify** reads `git diff --name-status` and assigns the PR one class from
  the paths it touches: `content` (records under `data/tentative/` or
  `data/staging/`), `tombstone` (a retraction appended to `data/trusted/`),
  `tooling` (scripts, workflows, schemas, the Lean tool programs, seeded
  modules), `docs`, or `promotion` (the bot moving records to trusted and
  regenerating modules). Two classes fail, except `docs` rides along with
  anything. Files the generator writes (`Tengoku/<Library>/**`,
  `Tengoku/All.lean`, `data/stats.json`) are never accepted from a person.
- **data-rules** (content, tombstone, promotion): `append-only` — every byte
  of an existing data file stays and new lines go at the end; `records` — each
  added record has the required fields, an allowed `source_url`, an identifier
  name that its statement declares, no duplicate against the PR or against
  trusted, and a corpus library's staging record carries `source_path` and
  `context` (without them it would never be compiled); `content-lint` — no
  `import`, `#eval`, `run_cmd`, `initialize`, `unsafe`, `native_decide`,
  `axiom`, `IO.Process`, or `set_option` off the allowlist inside a record.
- **credits**: no removed or changed line carrying an authorship or provenance
  marker (`Authors:`, `Copyright`, `source_url`, …). Scripts, workflows and
  schemas are exempt because they name those keys.
- **secrets**: TruffleHog for verified credentials, plus the same
  `detect-secrets` pattern scan as the pre-commit hook over every changed
  file and over the added lines of data files, so a token inside a record is
  caught too.
- **dco**: every commit carries `Signed-off-by:`.
- **depends**: `Depends-On: #N` lines in the description point at PRs that
  are merged or already in the queue.
- **lint-python**, **tooling-tests** (tooling only): `pre-commit run
  --all-files`, the unit tests, `actionlint` on the workflows.
- **sorry-advisory**: a comment listing `sorry`/`admit` in the change; never
  blocks, because the queue is the authority on proofs.
- **pr-gate**: the required check. Passes only when every job of the PR's
  class passed. It also posts **one comment per PR**, updated in place: each
  failed check with its step, the first lines of its error, what the check
  looks for, what to do, and — for the checks that reason about paths, text
  patterns or other services — a prefilled *Report a gate bug* issue link,
  because those checks can be wrong themselves.

Every `run:` step in every workflow runs under `bash -e -o pipefail`, so a
piped command's failure fails the step. That default exists because the
campaign found two checks whose findings never failed their job.

## 2. The merge queue

Runs on `merge_group`. GitHub forms groups of up to five PRs and tests them
cumulatively; a failing group loses its newest PR and the rest are retried.

1. **Cheap checks again** (classify, lint) on the merged result.
2. **Seed the cache**: `scripts/cache.sh get` fetches the newest published
   cache that is an ancestor of the merge commit and verifies each part's
   attestation (`TENGOKU_VERIFY=warn` until every published cache carries one,
   then `require`). Nothing is compiled that the cache already has.
3. **Corpus and candidates**: for every library the group touches,
   `scripts/ci/queue_targets.py` clones the corpus pinned in
   `schemas/sources.json` and runs `scripts/generate.py --candidate
   <source_path> --candidate-names <the group's own records>` — a candidate
   module holds the file's trusted records plus only this group's new ones,
   so an older broken staging record of the same file cannot sink someone
   else's PR.
4. **Build only the candidates**: `lake build <candidate modules>`; a
   `sorry` anywhere in the output fails the step with the record named.
5. **Axioms**: `lake exe tengoku-axioms --module <candidate>` walks every
   declaration of the module with Lean's `collectAxioms`; anything beyond the
   three standard axioms fails. This is the check that catches `decide
   +native`, which compiles cleanly and adds an axiom silently.
6. **Regeneration diff**: the library of every generated module the group
   touches is regenerated and compared; a hand edit cannot survive. Only the
   group's own files are compared, since `main` may lag the generator
   between promotions.
7. **Ejection comment**: when the group fails, the newest PR gets a comment
   with the file, line and column, the source line, the record name, a hint
   keyed on the error class (unknown identifier, type mismatch, unsolved
   goals, `sorry`, heartbeats, axiom, forbidden construct, regeneration), the
   run link, and the same *Report a gate bug* link.

## 3. What each check does and does not catch

- The gate reasons about **shape**, the queue about **mathematics**. A wrong
  proof always passes the gate and is always ejected by the queue; a
  mis-shaped PR never reaches the queue.
- Text rules have false positives by construction: the content lint matches a
  forbidden word inside a comment or string, the credits rule matches any
  removed line containing `Authors:`. The verdict comment says so and offers
  the report link.
- The secrets scan finds key ids, tokens and private keys inside JSON
  strings; it does not find a bare AWS secret-key value in one (the keyword
  rule needs the plain `key = value` form).
- The promotion class is granted by actor (`TENGOKU_BOT` repository variable)
  and then re-checked by the queue's regeneration diff, so even a correctly
  identified bot cannot hand-edit a generated file.
- A tombstone retracts a record everywhere the generator looks, including
  candidates; the bot's next promotion regenerates the module.
- Nothing here checks that a translation *means* the same as its source;
  that is Emissary-Archangel's job before a record is staged.

## 4. Reading a failure

**On the PR**: the checks list names the failed job; the verdict comment
names the step, quotes the error (`FAIL: …` lines become check-run
annotations, which the comment reads while the run is still in progress),
and says what to do. Push a fix and the gate re-runs; the comment updates in
place, and on success reads "all checks passed".

**In the queue**: the PR leaves the queue, auto-merge is disarmed, and the
ejection comment explains the failure. After fixing, re-queue with `gh pr
merge --squash --auto` or the *Merge when ready* button.

**If you think a check is wrong**: the *Report a gate bug* link opens an
issue with the PR, run, step and message filled in. A maintainer looks at
every one; a confirmed false positive becomes a unit test and a fix.

## 5. Running the tests yourself

```
python3 -m unittest scripts.ci.tests.test_gates -v        # 27 synthetic-repo cases
python3 -m unittest discover -s scripts/tests -v           # generator, promotion, stats
pipx install pre-commit && pre-commit run --all-files      # exactly what lint-python runs
```

To see what the queue will do with your records before you push:

```
scripts/cache.sh get                                       # newest cache; compiles nothing
git clone --filter=blob:none <corpus repo> corpora/<library>   # repo and commit from schemas/sources.json
python3 scripts/generate.py --corpus corpora/<library> --libraries <library> \
  --candidate <source_path> --candidate-names <your record names>
lake build Tengoku.<Library>.<Path>._candidate_<File>
lake build tengoku-axioms && lake env .lake/build/bin/tengoku-axioms --module Tengoku.<Library>.<Path>._candidate_<File>
```

## 6. The scenario campaign (the tests of the tests)

`scripts/ci/campaign/` opens real PRs against a sandbox copy of the repo and
checks that every check decides what it should. `gate.sh` holds 66
scenarios, each a one-line fixture with a precondition check (a fixture that
produced no change, or whose diff lacks the expected text, is refused) and
an expected failing job. `queue.sh` runs the merge-queue scenarios: every
ejection class one at a time, twelve clean PRs queued together, a broken PR
between two clean ones, a fix followed by a re-queue, a bulk promotion, a
hand edit disguised as a promotion. `guard4.sh` lands a workflow change on
`main` in the middle of a cache build and checks that the build relaunches on
the tip instead of publishing a tag the job token is not allowed to create.

The first full run (2026-09-15/16) found seven checks that passed when they
should have failed, all fixed the same night. The record of what ran and what
it found lives in the CompeteMath repository:
[`tests/tengoku-search/NOTES.md`](https://github.com/mikael-bashir/compete-math/blob/main/tests/tengoku-search/NOTES.md)
("Overnight campaign"). Run the campaign after any change to
`scripts/ci/`, the workflows or `schemas/`; it is the only thing that can
tell you a check has gone silent.

## 7. Adding a test

- A rule about records or paths: a case in `scripts/ci/tests/test_gates.py`.
  The `Repo` helper makes a throwaway git repository with one staging record,
  one trusted record, one generated module and one seeded module; write the
  change, commit, run the script, assert the exit code and the message.
- A rule about generated modules or promotion: `scripts/tests/`, with a
  fake `lake` on `PATH` where a build would be needed.
- A rule about the whole pipeline: one `sc` line in
  `scripts/ci/campaign/gate.sh`, or a `run_one` line in `queue.sh`, and run it
  against the sandbox.

## 8. Enforcement

The gate and the queue run on every PR today. They become *required* — and
direct pushes to `main` stop — once the banking pipeline (Emissary-Archangel's
staging hook and the promote loop) opens pull requests instead of pushing,
under a bot identity named in the `TENGOKU_BOT` variable. Until then a
failed check on a PR is advice, not a wall.
