# Tengoku (天国)

A growing corpus of Lean 4 **theorems and their proofs** — real, complete
proofs, not bare statements — harvested from open formalization libraries
and from CompeteMath's own certified problems.

Every entry already has a real proof from somewhere. The only question is
whether [Leak](https://competemath.com/leak) has stamped it:

- **`data/tentative/`** — a real proof from a real source (every record
  carries `source_url` pointing straight at it), which Leak has **not**
  re-verified with its own toolchain yet. Reason to believe it's correct;
  not yet Leak's own word for it.
- **`data/trusted/`** — a proof Leak's own toolchain has actually compiled
  and certified. `data/trusted/competemath.jsonl` is exactly this: it's
  read straight out of CompeteMath's `question_certificates` table, which
  only ever contains proofs Leak itself checked.

Promotion only ever goes one way, tentative → trusted, and only by Leak
actually re-verifying the proof — nothing here is trusted by assumption.

## Record shape

Each line in every `data/**/*.jsonl` file is one JSON record:

```json
{
  "name": "...",
  "statement": "theorem ... : ...",
  "proof": ":= by ...",
  "status": "tentative | trusted",
  "library": "...",
  "source_url": "...",
  "toolchain": "..."
}
```

## What's in `data/`

| File | Status | Source | Toolchain | Count |
|---|---|---|---|---|
| `tentative/compfiles.jsonl` | tentative | [dwrensha/compfiles](https://github.com/dwrensha/compfiles) | `leanprover/lean4:v4.34.0-rc1` | 6,042 |
| `trusted/competemath.jsonl` | trusted | CompeteMath's own certified problems | mixed (recorded per-row) | 262 |

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
declaration's name, statement, AND its full proof via a syntactic scan (no
build/elaboration required — see `lean_extract.py`), writing straight to
`data/tentative/<library>.jsonl`. Rerunnable against any library at any
time:

```bash
python3 tools/harvest.py --repo https://github.com/owner/name.git \
  --library name --toolchain leanprover/lean4:v4.34.0-rc2 \
  --out data/tentative/name.jsonl
```

`export-competemath-theorems.ts` produces `data/trusted/competemath.jsonl`
by reading already-Leak-certified proofs straight out of CompeteMath's
database (lives here for reference; actually run from the
[compete-math](https://github.com/mikael-bashir/compete-math) repo, where
the database connection is).

## Search

These records are indexed and searchable at
[competemath.com/tengoku](https://competemath.com/tengoku), status shown on
every result.
