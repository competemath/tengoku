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

## Every source in this seeding round

| Source | Files | Toolchain | Count |
|---|---|---|---|
| [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) — the community mathematics library itself | `tentative/mathlib-*.jsonl` (47 files, split by top-level module — `algebra`, `analysis`, `topology`, `numbertheory`, etc. — since one file would be ~120MB) | `leanprover/lean4:v4.34.0-rc2` | 188,989 |
| [teorth/equational_theories](https://github.com/teorth/equational_theories) — Terence Tao's project mapping relations between equational theories of magmas | `tentative/equational-theories.jsonl` | `leanprover/lean4:v4.29.1` | 13,193 |
| [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) — the Prime Number Theorem and related results | `tentative/primenumbertheoremand.jsonl` | `leanprover/lean4:v4.32.2` | 8,028 |
| [dwrensha/compfiles](https://github.com/dwrensha/compfiles) — catalog of competition problems formalized in Lean | `tentative/compfiles.jsonl` | `leanprover/lean4:v4.34.0-rc1` | 6,042 |
| [Prove2Me](https://prove2.me) — collaborative Lean formalization platform (missions + captains); harvested via its API, `source_url` links to each theorem's own Prove2Me page | `tentative/prove2me.jsonl` | mixed (recorded per-row) | growing to ~54,577 — see note below |
| [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) — DeepMind's formalized-conjectures benchmark (Erdős problems, Ben Green's 100 open problems, etc.); only the already-proven subset harvests here | `tentative/formal-conjectures.jsonl` | `leanprover/lean4:v4.33.1` | 2,584 |
| [fpvandoorn/Carleson](https://github.com/fpvandoorn/Carleson) — Carleson's theorem on pointwise convergence of Fourier series | `tentative/carleson.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 2,510 |
| [ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT) — Kevin Buzzard et al.'s formalization of Fermat's Last Theorem (ongoing; lemmas proven so far) | `tentative/flt.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 2,198 |
| [leanprover-community/batteries](https://github.com/leanprover-community/batteries) — the community standard library (Mathlib's own foundation) | `tentative/batteries.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 1,960 |
| [teorth/pfr](https://github.com/teorth/pfr) — Terence Tao, Yaël Dillies & Bhavik Mehta's formalization of the Polynomial Freiman-Ruzsa conjecture | `tentative/pfr.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 921 |
| CompeteMath's own certified problems | `trusted/competemath.jsonl` | mixed (recorded per-row) | 262 |

**~281,000 total** once Prove2Me's full harvest lands (currently running — its API needs 2 extra calls per theorem beyond the listing page, so pulling all ~54,577 takes on the order of an hour even with a bounded concurrent worker pool; this table will be updated with the final exact count).

**Considered and deliberately excluded**: [leanprover-community/lean-liquid](https://github.com/leanprover-community/lean-liquid) (the Liquid Tensor Experiment) — its `leanpkg.toml` pins `lean:3.48.0`, i.e. it's **Lean 3**, not Lean 4, and syntactically incompatible with everything else here. No standing OpenAI or EpochAI Lean *library* exists to harvest from either: OpenAI has published several independent single-result repos (each proving one theorem, e.g. their Navier–Stokes writeup), each pinned to its own toolchain with no shared library between them, and EpochAI's `LeanOpenProblems` is a scraping/tooling harness rather than a compiled Lean library itself.

Every harvested file is filtered for `sorry`: a declaration whose proof contains `sorry` anywhere isn't proven, no matter how confident-looking the rest of it is, and is silently dropped rather than mislabeled as tentative (see `lean_extract.py`'s `_contains_sorry`). This matters most for mixed-status sources like `formal-conjectures`, which stores solved and open problems side by side in the same files, and for Prove2Me, whose own theorem-listing endpoint always returns the posed (`sorry`) form — the real proof is fetched separately, from that theorem's own accepted submission.

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

## `tools/`

`harvest.py` clones a given Lean repo and extracts every `theorem`/`lemma`
declaration's name, statement, AND its full proof via a syntactic scan (no
build/elaboration required — see `lean_extract.py`), writing either to one
`data/tentative/<library>.jsonl` file, or — for a library too big for one
git-friendly file — split by top-level module into
`data/tentative/<library>-<module>.jsonl` files (this is how `mathlib-*`
was produced). Rerunnable against any library at any time:

```bash
# single output file
python3 tools/harvest.py --repo https://github.com/owner/name.git \
  --library name --toolchain leanprover/lean4:v4.34.0-rc2 \
  --out data/tentative/name.jsonl

# split by module (for a huge library)
python3 tools/harvest.py --repo https://github.com/owner/name.git \
  --library name --toolchain leanprover/lean4:v4.34.0-rc2 \
  --split-into data/tentative
```

`harvest_prove2me.py` pulls proved theorems + their accepted solutions from
the [Prove2Me](https://prove2.me) API (needs an agent API key, env var
`PROVE2ME_API_KEY` — never committed, never passed on the command line).
Each theorem needs 2 extra API calls beyond the listing page, so fetches
run concurrently (bounded worker pool) with retry+backoff on transient
failures — a full pull of 50,000+ theorems is on the order of an hour, not
a day:

```bash
export PROVE2ME_API_KEY=...
python3 tools/harvest_prove2me.py --out data/tentative/prove2me.jsonl
# or bound it for a quicker partial pull: --max 500
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
