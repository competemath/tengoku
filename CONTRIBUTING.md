# Contributing to Tengoku

Everything lands through a pull request; a gate checks the shape of the
change in about three minutes, and a merge queue compiles exactly the
mathematics it adds. You never build the whole tree, and you never wait for a
person unless a check thinks it might be wrong. [How Tengoku is
tested](docs/testing.md) explains every check; this page is the short list of
the easiest way to do each thing.

## Add theorems

1. Write your records, one JSON object per line, into a **new file**
   `data/staging/<library>/<anything>.jsonl` (`schemas/record.schema.json`
   is the shape; a record of a library that has a corpus in
   `schemas/sources.json` needs `source_path` and `context`, or it is never
   compiled). One file per PR: two PRs appending to the same file cannot both
   sit in the queue.
2. Check it builds before you push (nothing here compiles the tree):
   ```
   scripts/cache.sh get
   git clone --filter=blob:none <corpus repo> corpora/<library>   # repo + commit in schemas/sources.json
   python3 scripts/generate.py --corpus corpora/<library> --libraries <library> \
     --candidate <source_path> --candidate-names <your record names, comma-separated>
   lake build Tengoku.<Library>.<Path>._candidate_<File>
   ```
3. `git commit -s` (the sign-off is required), push, open the PR, and turn on
   *Merge when ready*. The gate comments on the PR with anything it found;
   the queue builds your candidate module and merges.
4. The promote bot later moves your records to `data/trusted/`, regenerates
   the module and deletes your per-PR file in its own PR. Your name, and the
   `source_url`, stay on the record forever.

## Retract a theorem

Append a tombstone line to `data/trusted/<library>.jsonl` — never delete the
record:

```
{"tombstone": "<name>", "reason": "…", "by": "<you>", "at": "<ISO date>"}
```

The generator drops the record from its module and from every candidate; the
bot's next promotion regenerates the module. History stays in the file.

## Add a source library

A tooling PR that adds the source to `schemas/sources.json` (its URL prefix,
its licence, and its `corpora` entry: repository and commit the generator
reads source files from). Records from it come in a second PR.

## Change the tooling

Scripts, workflows, schemas and the Lean tool programs are `tooling`. Install
the hooks once (`pipx install pre-commit && pre-commit install`); CI runs the
same `.pre-commit-config.yaml`, the unit tests and `actionlint`, so what
passes locally passes there. `CODEOWNERS` review applies. Run the scenario
campaign against the sandbox before touching `scripts/ci/` or the workflows
(`scripts/ci/campaign/README.md`).

## Fix docs

`README.md`, `CONTRIBUTING.md` and `docs/**` are `docs`; they may ride along
with any other change.

## When a check fails

Read the gate's comment on your PR: it names the check and the step, quotes
the error, and says what to do. Push the fix; the comment updates. If the PR
was in the queue, re-queue it after the fix (`gh pr merge --squash --auto`).
If you believe the check is wrong, use the **Report a gate bug** link in the
comment — it opens an issue with everything filled in.

## Depend on another PR

Put `Depends-On: #123` in your description. Your PR waits until #123 is
merged or queued ahead of it; the gate re-runs when the description or the
branch changes.

## For maintainers

- **The promote bot** is the only identity whose PRs may touch generated
  files (`promotion` class); the account is named in the `TENGOKU_BOT`
  repository variable. The queue still regenerates and diffs what it touches.
- **Porting tooling changes**: prove them in the sandbox
  (`competemath/tengoku-sandbox`) with the campaign, then open the same
  change here.
- **Caches** are built nightly by CI on Linux; `scripts/cache.sh put` refuses
  to pack on macOS. Merging a workflow change while a build runs makes that
  build relaunch on the tip instead of publishing.
- **Gate-bug issues** are the feedback loop: a confirmed false positive
  becomes a unit test and a fix.
