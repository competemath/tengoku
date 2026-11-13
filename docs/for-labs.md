# Using Tengoku as training data

Tengoku is Apache-2.0, and each source library stays under its own licence (listed in [the allowlist](../schemas/sources.json)). All of them permit training. You do not need to ask us first. This page is the short version of what to do.

## What the licences require

1. **Keep the notices.** Keep the copyright and attribution notices of everything you reproduce, and ship [NOTICE](../NOTICE) and the licence texts alongside (Apache-2.0 section 4).
2. **Say what you changed.** A modified copy states its changes (section 4(b)).
3. **Do not imply endorsement.** Do not use the name "CompeteMath", or the names of its services, to suggest they back your model or dataset.

## What we ask

- **Cite it, and say which commit.** Cite Tengoku ([10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400)) in your dataset or model documentation, with the commit you used. Versioned releases are rare, so a commit hash is the reliable version (see [releases](releases.md)).
- **Keep the credit with each example.** A record's `library`, `source_url` and `Author:` line should travel with it into any dataset you publish.
- **Re-sync before each new training run.** Sometimes a record is retracted or a library or module is removed. Pull the latest and drop what has gone: tombstone lines in `data/trusted/`, libraries no longer in the allowlist, and modules with a marker in `data/raze/` ([PR classes](pr-classes.md), section 8). A removed library can come back rebuilt, so do not mix in old copies. Drop them from any data you publish as well. This applies to future runs; we do not ask you to change a model you have already trained.
- **Decontaminate.** Tengoku includes public formalisations of competition problems (Compfiles, IMO shortlist). Check for overlap before you report results on miniF2F, PutnamBench or similar.
- **Describe `trusted` accurately.** It means the automated checks passed (builds, no `sorry`, standard axioms only, assumptions not contradictory). It does not mean a mathematician has read the statement.

## Bulk data and the hosted services

Take bulk data from this repository and its releases. The search API, the MCP tools and Leak are for interactive use, and crawling them may be blocked.

## Problems

A wrong statement, a credit that should change, or a removal request: [open an issue](https://github.com/competemath/tengoku/issues/new).
