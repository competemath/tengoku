# Tengoku (天国)

A growing corpus of Lean 4 **theorem statements** — not proofs — harvested
from open formalization libraries and from CompeteMath's own certified
problems, staged for [Leak](https://competemath.com/leak) to attempt.

Every record is a name, a statement, where it came from, and the Lean
toolchain it was written against. Nothing here has a proof attached on
purpose: this is a target list for an automated prover, not an archive of
finished work.

## What's in `data/`

| File | Source | Toolchain | Count |
|---|---|---|---|
| `compfiles.jsonl` | [dwrensha/compfiles](https://github.com/dwrensha/compfiles) | `leanprover/lean4:v4.34.0-rc1` | 6,042 |
| `competemath.jsonl` | CompeteMath's own certified problems | mixed (recorded per-row) | 262 |

Each line is one JSON record:

```json
{"name": "...", "statement": "theorem ... : ...", "library": "...", "source_url": "...", "toolchain": "..."}
```

## Why `v4.34.0-rc2` is the target toolchain going forward

Nearly every serious Lean formalization project depends on Mathlib and
tracks a Mathlib-compatible `lean-toolchain`, so maximizing the reachable
union of theorems is mostly a question of which Mathlib release the most
dependent projects have already migrated to — not picking a novel toolchain.
As of this repo's creation, Mathlib's own `master` (and its immediate
dependency graph — Batteries, Aesop, Qq, ProofWidgets4) is pinned to
`leanprover/lean4:v4.34.0-rc2`, and both `ImperialCollegeLondon/FLT` and
`fpvandoorn/Carleson` already match it exactly. `compfiles` trails by one
release candidate (`v4.34.0-rc1`) — close enough to harvest as-is.

No standing OpenAI or EpochAI Lean *library* exists to harvest from: OpenAI
has published several independent single-result repos (each proving one
theorem, e.g. their Navier–Stokes writeup), each pinned to its own toolchain
with no shared library between them, and EpochAI's `LeanOpenProblems` is a
scraping/tooling harness rather than a compiled Lean library itself.

## `tools/`

`harvest.py` clones a given Lean repo and extracts every `theorem`/`lemma`
declaration's name + signature via a syntactic scan (no build/elaboration
required — see `lean_extract.py`), producing one more `data/*.jsonl` file.
Rerunnable against any library at any time:

```bash
python3 tools/harvest.py --repo https://github.com/owner/name.git \
  --library name --toolchain leanprover/lean4:v4.34.0-rc2 \
  --out data/name.jsonl
```

`competemath.jsonl` is produced separately, by a script that lives in the
[compete-math](https://github.com/mikael-bashir/compete-math) repo
(`scripts/export-competemath-theorems.ts`), since it reads CompeteMath's own
database.

## Search

These records are indexed and searchable at
[competemath.com/tengoku](https://competemath.com/tengoku).
