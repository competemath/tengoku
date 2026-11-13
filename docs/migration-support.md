# Migration support: a proposal

> **This is a proposal, not a status the tree has.** Nothing in the gates, the queue or the scripts uses it, and no `data/migrations/` folder exists. It
> says how a library bump (a reseed such as Tau Ceti's) could be made safe for projects that build on Tengoku. Anything marked *assumed* was not checked.

## The problem

A bump removes or rebuilds modules of one library. A project that builds on Tengoku (Tengai today, others later) can break in three ways:

1. a module it imports is gone or has another path;
2. a theorem it names is gone, renamed, or has a different statement;
3. a notation or instance it relied on is scoped, local or gone.

Today a consumer learns of this when its build fails after it moves its pin. Nothing tells it what changed, and nothing stops it moving.

## What exists now (read in the repository, 2026-11-13)

- A library's theorems are listed in `data/intake/<library>/manifest.jsonl`, one line each: `name`, `statement`, `module`, `source_path`, `library`, `source_url` (the
  upstream commit), `toolchain`, `via`. Tau Ceti's has 35,358 lines.
- `data/intake/<library>/parts/NNN.json` is each part's report (`bundle_sha256`, `modules`, `theorems`). `data/raze/<id>.json` records a removal and why
  ([PR classes](pr-classes.md) section 8).
- A bump is the factory's `bump-library` run, then a raze of the old modules, then the new parts as an intake PR and extend PRs ([PR classes](pr-classes.md)
  sections 6 and 8). Between the raze and the last part the library is absent or partial.
- Tengai pins one Tengoku commit in `tengoku.pin` and takes that commit's compiled cache (`scripts/tengoku-setup.sh`). Its `--latest` option moves the pin to the
  commit of the newest published cache and checks nothing else.
- Because a pin is a commit, a pinned consumer is never broken by a bump. The break comes when it moves.

## Proposal

### 1. A migration record for every reseed

A reseed ends with one PR that adds `data/migrations/<library>-<date>/`:

| File | Content |
| --- | --- |
| `summary.json` | `library`, `from` and `to` (each: Tengoku commit, upstream `source_url` commit, toolchain), counts per change, the migration's id |
| `names.jsonl` | one line per theorem whose name, module or statement changed: `{"old", "new", "change", "old_module", "new_module"}` |
| `modules.jsonl` | one line per module removed, added or moved |

`change` is one of `moved` (same name, other module), `renamed` (same statement once the declared name is removed, other name), `restated` (same name, different
statement), `removed`, `added`. Unchanged names are not listed. A theorem that cannot be placed in one class is `removed` plus `added`; the record never guesses.

The files are **computed from git**, not written by hand: the manifest at `from.commit` against the manifest at the PR's base. That is what makes them checkable (section 2).
*Assumed:* matching renames by statement text is good enough for a first version. The isnad id (`docs/isnad.md`) is a better key once the library's modules are tagged;
the manifest does not carry it today.

### 2. A `migration` PR class, recomputed

Like restructure (section 5 of [PR classes](pr-classes.md)) and roots (section 11): the gate runs the **base commit's** `scripts/migration_tree.py` on the two manifests and
accepts a PR only if it equals that output byte for byte and changes nothing else. Any author may send it. A code owner reviews it, because it is the statement
of what a reseed broke. The merge queue repeats the check on the entry's base and builds nothing.

A reseed is not complete until this PR has merged. Until then the library is "in reseed", and the migration record says so (section 5).

### 3. A codemod for consumers

`scripts/migrate.py --map data/migrations/<id> <path>...` rewrites a consumer's `.lean` files:

- `import` lines and fully qualified names, exactly;
- an unqualified use under `open` or `namespace`, a `restated` theorem and a `removed` one are **reported with file and line, not rewritten**, as the roots script reports an unresolved root.

It writes a patch and a report, never silently changes a statement. No compatibility shims and no `@[deprecated]` aliases are added to the tree: they would double theorem counts in a
cache that has already hit 102 GB, and an alias in the root namespace is the clash the roots class removes.

### 4. A consumer registry

`schemas/consumers.json`, one entry per project that builds on Tengoku:

```json
{"name": "tengai", "repo": "https://github.com/competemath/tengai", "kind": "internal",
 "pin_file": "tengoku.pin", "branch": "main", "build": "lake build"}
```

- **internal**: when a migration PR merges, a workflow opens a PR in the consumer that moves its pin to the first commit with a published cache after the migration, runs
  `migrate.py`, and builds. The consumer's own CI is the proof. The PR says what the codemod left.
- **external**: the project registers itself with a PR here (`kind: "external"`). The same workflow builds it and posts the result **on the Tengoku migration PR only**
  as an advisory comment. It opens nothing in a repository whose owner did not register it.

The workflow runs at a migration merge, not on every PR (a consumer's build is a Lake build against the tree's cache).

### 5. A guard on moving the pin

`scripts/pin.sh` (and the copy in a consumer, such as `tengoku-setup.sh`) reads `data/migrations/index.json`, a list of `{id, library, commit}`. Moving a pin across any
entry's commit, or to a commit while a library is in reseed, stops and prints the migration's path unless the caller passes `--accept-migrations`. `--latest` never lands
inside a reseed. The guard only reads a committed file; it adds no network call beyond the one `--latest` already makes.

### 6. Say it in the release notes

The snapshot release already has an "Upgrade impact" heading (v1.0.0 says "None: this is the first release"). A migration adds its summary there, and the rule for
what bumps a major version is written once in [releases](releases.md): a rename or removal of a trusted name or module path is major.

## What this does not do

- It does not make `main` stable. Consumers who track `main` are told what changed, not protected from it.
- It does not decide what is stable. That is a policy for the maintainer (the list of what a consumer may rely on).
- It does not predict what upstream will rename in the next commit of Tau Ceti; it reports what the new tree turned out to be.
- It does not keep two revisions of a library side by side. Names would clash in one namespace, and the queue's 40-minute limit (about 300 modules) rules out an atomic swap of a
  4,463-module library in one entry.

## Rollout

| Phase | Work | Done when |
| --- | --- | --- |
| 0 | `migration_tree.py` and `migrate.py` with tests; a rehearsal on a small library in `tengoku-sandbox`; Tengai as the first registry entry (no workflow) | the rehearsal's record is reproduced byte for byte from two commits, and the codemod's patch builds on a fixture consumer |
| 1 | the `migration` class in the gate and the queue; `data/migrations/index.json` | a sandbox migration PR passes the gate and the queue |
| 2 | the pin guard in `scripts/pin.sh`; the consumer workflow for `internal` | Tengai's pin PR opens and builds on a sandbox migration |
| 3 | external registration | one external consumer has registered, and its advisory result appears |

Nothing here needs a Tau Ceti bump to start: Tau Ceti is the first real use, not the test.

## Assumed, not checked

- That a theorem's `statement` in the manifest, with the declared name removed, is stable under a bump that changes only the name.
- That `scripts/pin.sh` is the right place for the guard; this proposal did not read it.
- That the first commit after a migration with a published cache is available soon enough (caches are nightly).
- That Tengai (3 Lean modules at its PR #1) imports nothing from a library being bumped; its Lean files were not read.
- The cost of a consumer build on a runner, and the size of `names.jsonl` for a 35,000-theorem library.

## Questions for the maintainer

1. Is a reseed allowed to leave the library absent or partial for a day (as navier-stokes-euler was), or must the migration PR be the first thing to merge?
2. Should an external consumer's failure ever block a migration, or is it advisory only (this proposal says advisory)?
3. Who may register as `internal`: any repository of the organisation, or a list kept here?
