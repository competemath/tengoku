# Tengoku (天国)

An expanding knowledge-tree of Lean 4 **theorems and their proofs** — harvested from open formalization libraries
and from CompeteMath's own research.

Every entry already has a real proof from somewhere. The distinction is
whether [Leak](https://competemath.com/leak) has stamped it:

- **`data/tentative/`** — a real proof from a real source (every record
  carries `source_url` pointing straight at it), which Leak has **not**
  re-verified with its own toolchain yet. Reason to believe it's correct;
  Leak doesn't yet vouch for it.
- **`data/trusted/`** — a proof Leak's own toolchain has actually compiled
  and certified.

Promotion only ever goes one way, tentative → trusted, and only by Leak
actually re-verifying the proof — nothing here is trusted, even by reasonable assumption.

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
| [Prove2Me](https://prove2.me) — collaborative Lean formalization platform (missions + captains); harvested via its API, `source_url` links to each theorem's own Prove2Me page | `tentative/prove2me-001.jsonl` … `prove2me-040.jsonl` (40 files, split by byte size — one file would be ~1.7GB) | mixed (recorded per-row): 38,170 on `v4.33.1`, 12,019 on `v4.29.0`, 4,268 on `v4.30.0` | 54,457 |
| [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) — DeepMind's formalized-conjectures benchmark (Erdős problems, Ben Green's 100 open problems, etc.); only the already-proven subset harvests here | `tentative/formal-conjectures.jsonl` | `leanprover/lean4:v4.33.1` | 2,584 |
| [fpvandoorn/Carleson](https://github.com/fpvandoorn/Carleson) — Carleson's theorem on pointwise convergence of Fourier series | `tentative/carleson.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 2,510 |
| [ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT) — Kevin Buzzard et al.'s formalization of Fermat's Last Theorem (ongoing; lemmas proven so far) | `tentative/flt.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 2,198 |
| [leanprover-community/batteries](https://github.com/leanprover-community/batteries) — the community standard library (Mathlib's own foundation) | `tentative/batteries.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 1,960 |
| [teorth/pfr](https://github.com/teorth/pfr) — Terence Tao, Yaël Dillies & Bhavik Mehta's formalization of the Polynomial Freiman-Ruzsa conjecture | `tentative/pfr.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 921 |
| CompeteMath's own certified problems | `trusted/competemath.jsonl` | mixed (recorded per-row) | 262 |
| [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem) — Claude's complete, independent Lean 4 formalization of Fermat's Last Theorem (Sept 2026) | `tentative/flt-anthropic-001.jsonl` … `flt-anthropic-003.jsonl` (split by byte size — one file would be ~110MB) | `leanprover/lean4:v4.33.1` | 48,501 |
| [leanprover-community/physlib](https://github.com/leanprover-community/physlib) — physics results (classical mechanics, QFT, quantum info) | `tentative/physlib.jsonl` | `leanprover/lean4:v4.33.0` | 10,571 |
| [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) — first/second-order logic completeness, Gödel's incompleteness theorems, modal logic | `tentative/foundation.jsonl` | `leanprover/lean4:v4.33.1` | 5,559 |
| [leanprover-community/con-nf](https://github.com/leanprover-community/con-nf) — consistency of Quine's New Foundations set theory | `tentative/con-nf.jsonl` | `leanprover/lean4:v4.21.0-rc3` | 2,785 |
| [mortarsanjaya/IMOSLLean4](https://github.com/mortarsanjaya/IMOSLLean4) — IMO Shortlist problems (2006+, all categories except Geometry) | `tentative/imoshortlist.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 2,330 |
| [sinhp/HoTTLean](https://github.com/sinhp/HoTTLean) — sorry-free groupoid model of homotopy type theory | `tentative/hottlean.jsonl` | `leanprover/lean4:v4.25.0-rc2` | 2,122 |
| [lecopivo/SciLean](https://github.com/lecopivo/SciLean) — scientific computing (differential equations, automatic differentiation) | `tentative/scilean.jsonl` | `leanprover/lean4:v4.28.0-rc1` | 1,833 |
| [leanprover-community/sphere-eversion](https://github.com/leanprover-community/sphere-eversion) — existence of sphere eversions | `tentative/sphere-eversion.jsonl` | `leanprover/lean4:v4.33.0` | 892 |
| [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion) — construction of Brownian motion, Kolmogorov–Chentsov continuity | `tentative/brownian-motion.jsonl` | `leanprover/lean4:v4.33.0-rc1` | 1,441 |
| [scottnarmstrong/DeGiorgi](https://github.com/scottnarmstrong/DeGiorgi) — De Giorgi–Nash–Moser elliptic PDE regularity theory | `tentative/degiorgi.jsonl` | `leanprover/lean4:v4.29.0-rc6` | 1,192 |
| [trishullab/PutnamBench](https://github.com/trishullab/PutnamBench) — Putnam Competition (1962–2025) formalizations, Lean 4 subset | `tentative/putnambench.jsonl` | `leanprover/lean4:v4.27.0` | 524 |
| [Ivan-Sergeyev/seymour](https://github.com/Ivan-Sergeyev/seymour) — Seymour's decomposition theorem for regular matroids | `tentative/seymour.jsonl` | `leanprover/lean4:v4.18.0` | 468 |
| [mo271/FormalBook](https://github.com/mo271/FormalBook) — formalizing "Proofs from THE BOOK" (Aigner–Ziegler) | `tentative/formalbook.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 279 |
| [loganrjmurphy/LeanEuclid](https://github.com/loganrjmurphy/LeanEuclid) — autoformalization benchmark for Euclidean geometry | `tentative/leaneuclid.jsonl` | `leanprover/lean4:v4.19.0` | 206 |
| [leanprover-community/flt-regular](https://github.com/leanprover-community/flt-regular) — Kummer's proof of FLT for regular primes | `tentative/flt-regular.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 195 |
| [emilyriehl/infinity-cosmos](https://github.com/emilyriehl/infinity-cosmos) — basic formal theory of ∞-cosmoi | `tentative/infinity-cosmos.jsonl` | `leanprover/lean4:v4.34.0-rc1` | 134 |
| [CBirkbeck/DirichletNonvanishing](https://github.com/CBirkbeck/DirichletNonvanishing) — non-vanishing of Dirichlet L-functions on Re(s)=1 | `tentative/dirichletnonvanishing.jsonl` | `leanprover/lean4:v4.13.0-rc3` | 118 |
| [YaelDillies/LeanCamCombi](https://github.com/YaelDillies/LeanCamCombi) — Cambridge combinatorics courses | `tentative/leancamcombi.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 61 |
| [Robby955/FormalSLT](https://github.com/Robby955/FormalSLT) — statistical learning theory (concentration, generalization bounds) | `tentative/formalslt.jsonl` | `leanprover/lean4:v4.32.2` | 8,583 |
| [math-inc/Sphere-Packing-Lean](https://github.com/math-inc/Sphere-Packing-Lean) — sphere packing optimality in dimensions 8 and 24 (Viazovska et al.) | `tentative/sphere-packing-ext.jsonl` | `leanprover/lean4:v4.28.0` | 2,818 |
| [formal-applied-math/formal-mathfin](https://github.com/formal-applied-math/formal-mathfin) — formally verified mathematical finance (Black-Scholes, FTAP, Merton) | `tentative/formal-mathfin.jsonl` | `leanprover/lean4:v4.32.0` | 2,885 |
| [Lean-MoDS/StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib) — probability/statistics/ML (concentration, empirical processes, random matrices) | `tentative/statsmllib.jsonl` | `leanprover/lean4:v4.33.0` | 2,218 |
| [thefundamentaltheor3m/Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) — sphere packing optimality in dimension 8 (the original project) | `tentative/sphere-packing-orig.jsonl` | `leanprover/lean4:v4.32.0` | 923 |
| [mbrcic/ai-safety-formalization-atlas](https://github.com/mbrcic/ai-safety-formalization-atlas) — AI-safety-relevant claims formalized as Lean proofs | `tentative/aisafety-atlas.jsonl` | `leanprover/lean4:v4.33.0` | 715 |
| [logical-intelligence/erdos-unit-distance](https://github.com/logical-intelligence/erdos-unit-distance) — a second, independent formalization of Alpöge's disproof of the Erdős unit-distance conjecture | `tentative/erdos-unit-distance-2.jsonl` | `leanprover/lean4:v4.29.1` | 706 |
| [math-inc/strongpnt](https://github.com/math-inc/strongpnt) — the strong Prime Number Theorem, AI-formalized | `tentative/strongpnt.jsonl` | `leanprover/lean4:v4.21.0` | 1,077 |
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) — sorry-free statistical learning theory library | `tentative/leanslt.jsonl` | `leanprover/lean4:v4.32.0` | 1,663 |
| [urikol/QuantumOptimization](https://github.com/urikol/QuantumOptimization) — machine-verified quantum-optimization formalizations | `tentative/quantumoptimization.jsonl` | `leanprover/lean4:v4.28.0` | 1,400 |
| [djvelleman/HTPILeanPackage](https://github.com/djvelleman/HTPILeanPackage) — tactics and exercises for "How to Prove It" | `tentative/htpi.jsonl` | `leanprover/lean4:v4.33.0` | 384 |
| [project-numina/LeanGeo](https://github.com/project-numina/LeanGeo) — geometry competition problems | `tentative/leangeo.jsonl` | `leanprover/lean4:v4.15.0` | 395 |
| [math-inc/FrontierMathOpen-Hypergraphs](https://github.com/math-inc/FrontierMathOpen-Hypergraphs) — an Epoch AI FrontierMath hypergraph/Ramsey-theoretic problem | `tentative/frontiermath-hypergraphs.jsonl` | `leanprover/lean4:v4.28.0` | 340 |
| [ctchou/AutomataTheory](https://github.com/ctchou/AutomataTheory) — finite automata theory | `tentative/automatatheory.jsonl` | `leanprover/lean4:v4.24.0-rc1` | 231 |
| [AnandGokhale/LeanForControl](https://github.com/AnandGokhale/LeanForControl) — database of control-theory proofs | `tentative/leanforcontrol.jsonl` | `leanprover/lean4:v4.30.0-rc2` | 184 |
| [math-inc/Erdos1196](https://github.com/math-inc/Erdos1196) — Erdős Problem #1196 (bound on ∑1/(a·log a) for primitive sets) | `tentative/erdos1196.jsonl` | `leanprover/lean4:v4.30.0-rc1` | 122 |
| [kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance) — Kim Morrison's formalization of Alpöge's disproof of the Erdős unit-distance conjecture | `tentative/erdos-unit-distance-1.jsonl` | `leanprover/lean4:v4.32.2` | 102 |
| [harmonic-ai/IMO2025](https://github.com/harmonic-ai/IMO2025) — Harmonic's Aristotle system, 5 of 6 IMO 2025 problems | `tentative/imo2025-harmonic.jsonl` | `leanprover/lean4:v4.20.0-rc5` | 95 |
| [MoonshotAI/CombiBench](https://github.com/MoonshotAI/CombiBench) — combinatorics competition benchmark | `tentative/combibench.jsonl` | `leanprover/lean4:v4.24.0` | 14 |
| [optpku/CAM-Bench](https://github.com/optpku/CAM-Bench) — competition/applied-math proof targets | `tentative/cambench.jsonl` | `leanprover/lean4:v4.28.0` | 11 |
| [math-inc/KakeyaFiniteFields](https://github.com/math-inc/KakeyaFiniteFields) — the Kakeya set problem over finite fields | `tentative/kakeya-finitefields.jsonl` | `leanprover/lean4:v4.26.0-rc2` | 9 |
| [shetzl/autth](https://github.com/shetzl/autth) — finite automata and context-free grammars | `tentative/autth.jsonl` | `leanprover/lean4:v4.12.0-rc1` | 3 |
| [ColinBundschu/mass-gap](https://github.com/ColinBundschu/mass-gap) — Yang-Mills mass gap over compact simple groups | `tentative/mass-gap.jsonl` | `leanprover/lean4:v4.32.2` | 11,043 |
| [LionSR/TNLean](https://github.com/LionSR/TNLean) — tensor-network theory | `tentative/tnlean.jsonl` | `leanprover/lean4:v4.34.0-rc1` | 10,383 |
| [siqiliu-tsinghua/tautology](https://github.com/siqiliu-tsinghua/tautology) — the reals constructed and formalized from nothing, without Mathlib | `tentative/tautology.jsonl` | `leanprover/lean4:v4.30.0` | 9,658 |
| [Verified-zkEVM/VCVio](https://github.com/Verified-zkEVM/VCVio) — machine-checked cryptographic proofs | `tentative/vcvio.jsonl` | `leanprover/lean4:v4.33.1` | 6,621 |
| [Verified-zkEVM/ArkLib](https://github.com/Verified-zkEVM/ArkLib) — formally verified arguments-of-knowledge (SNARK-adjacent) library | `tentative/arklib.jsonl` | `leanprover/lean4:v4.33.1` | 4,562 |
| [schildep/verified-3d-mesh-intersection](https://github.com/schildep/verified-3d-mesh-intersection) — formally verified 3D mesh intersection (CSG) algorithm correctness | `tentative/verified-3d-mesh-intersection.jsonl` | `leanprover/lean4:v4.15.0` | 3,753 |
| [EvolvingPrograms/erdos-simonovits-degeneracy](https://github.com/EvolvingPrograms/erdos-simonovits-degeneracy) — machine-checked disproof of the Erdős–Simonovits degeneracy conjecture | `tentative/erdos-simonovits-degeneracy.jsonl` | `leanprover/lean4:v4.32.0` | 1,435 |
| [uda-lab/leray-hopf](https://github.com/uda-lab/leray-hopf) — Leray–Hopf weak solutions for Navier–Stokes | `tentative/leray-hopf.jsonl` | `leanprover/lean4:v4.31.0-rc2` | 1,151 |
| [schildep/verified-polygon-intersection](https://github.com/schildep/verified-polygon-intersection) — formally verified polygon intersection algorithm correctness | `tentative/verified-polygon-intersection.jsonl` | `leanprover/lean4:v4.15.0` | 942 |
| [VTrelat/ZFLean](https://github.com/VTrelat/ZFLean) — practical framework for set-theoretic development | `tentative/zflean.jsonl` | `leanprover/lean4:v4.33.0` | 890 |
| [Zetetic-Dhruv/formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) — a kernel for synthetic formalization of statistical learning theory | `tentative/formal-learning-theory-kernel.jsonl` | `leanprover/lean4:v4.29.0-rc6` | 651 |
| [Shreyas4991/Algolean](https://github.com/Shreyas4991/Algolean) — algorithms & complexity library | `tentative/algolean.jsonl` | `leanprover/lean4:v4.33.0` | 364 |
| [WuProver/groebner_proj](https://github.com/WuProver/groebner_proj) — Gröbner basis theory | `tentative/groebner-proj.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 327 |
| [jsm28/AperiodicMonotilesLean](https://github.com/jsm28/AperiodicMonotilesLean) — the aperiodic "hat tile"/einstein monotile | `tentative/aperiodicmonotiles.jsonl` | `leanprover/lean4:v4.34.0-rc2` | 311 |
| [ProofOfKeags/btc-verified](https://github.com/ProofOfKeags/btc-verified) — verified Bitcoin protocol components | `tentative/btc-verified.jsonl` | `leanprover/lean4:v4.30.0-rc2` | 218 |
| [teorth/expdb](https://github.com/teorth/expdb) — analytic number theory exponent database | `tentative/expdb.jsonl` | `leanprover/lean4:v4.32.0` | 194 |
| [b-mehta/ABC-Exceptions](https://github.com/b-mehta/ABC-Exceptions) — constructions of exceptions to the ABC conjecture | `tentative/abc-exceptions.jsonl` | `leanprover/lean4:v4.21.0-rc3` | 192 |
| [a2435191/lean-logic-formalization](https://github.com/a2435191/lean-logic-formalization) — formalization of van den Dries's "Logic Notes" | `tentative/lean-logic-formalization.jsonl` | `leanprover/lean4:v4.20.0-rc5` | 174 |
| [verified-optimization/CvxLean](https://github.com/verified-optimization/CvxLean) — convex optimization modeling with verified correctness | `tentative/cvxlean.jsonl` | `leanprover/lean4:v4.8.0-rc1` | 150 |
| [hanwenzhu/miller-rabin](https://github.com/hanwenzhu/miller-rabin) — Miller–Rabin primality test correctness proof | `tentative/miller-rabin.jsonl` | `leanprover/lean4:v4.22.0` | 80 |
| [lengyijun/goldbach_tm](https://github.com/lengyijun/goldbach_tm) — Goldbach conjecture encoded as a 25-state Turing machine | `tentative/goldbach-tm.jsonl` | `leanprover/lean4:v4.14.0-rc2` | 83 |
| [vltanh/lean4-analysis-tao](https://github.com/vltanh/lean4-analysis-tao) — formalization of Tao's "Analysis I" | `tentative/lean4-analysis-tao.jsonl` | `leanprover/lean4:v4.29.0` | 66 |
| [keilambda/ttfpi](https://github.com/keilambda/ttfpi) — "Type Theory and Formal Proof: An Introduction" | `tentative/ttfpi.jsonl` | `leanprover/lean4:v4.13.0` | 49 |
| [math-inc/RiemannHypothesisCurves](https://github.com/math-inc/RiemannHypothesisCurves) — the Riemann Hypothesis for curves (function-field analogue) | `tentative/riemannhypothesiscurves.jsonl` | `leanprover/lean4:v4.26.0-rc2` | 49 |
| [math-inc/ZkLinalg](https://github.com/math-inc/ZkLinalg) — formal security proof of Reed-Solomon IOP-of-proximity constructions | `tentative/zklinalg.jsonl` | `leanprover/lean4:v4.24.0` | 48 |
| [lenianiva/Prismriver](https://github.com/lenianiva/Prismriver) — music theory formalization + DSL | `tentative/prismriver.jsonl` | `leanprover/lean4:v4.28.0` | 52 |
| [PnVDiscord/software-foundations-lean](https://github.com/PnVDiscord/software-foundations-lean) — "Software Foundations" ported to Lean 4 | `tentative/software-foundations-lean.jsonl` | `leanprover/lean4:v4.21.0` | 37 |
| [jsm28/IMOShortlist2024Lean](https://github.com/jsm28/IMOShortlist2024Lean) — 2024 IMO Shortlist formalizations | `tentative/imoshortlist2024.jsonl` | `leanprover/lean4:v4.22.0-rc3` | 34 |
| [stepchowfun/proofs](https://github.com/stepchowfun/proofs) — general formally verified mathematics | `tentative/stepchowfun-proofs.jsonl` | `leanprover/lean4:v4.33.1` | 26 |
| [T-Brick/lean-wasm](https://github.com/T-Brick/lean-wasm) — formalization of the WebAssembly spec | `tentative/lean-wasm.jsonl` | `leanprover/lean4:v4.25.0` | 11 |

**437,612 indexed and searchable** across 81 libraries (a small number of
harvested declarations with no extractable proof body — mostly
`axiom`/opaque-style entries the syntactic extractor can't pull a proof
out of — are dropped at import rather than counted here; see
`import-tengoku.ts`'s validation).

**Note on anthropics/fermats-last-theorem**: that repo's own tree also
contains a `P2M/` directory vendoring ~552,000 declarations from Prove2Me
(already harvested here directly, under `library: "prove2me"`) — those are
excluded from `flt-anthropic.jsonl` to avoid double-counting and
misattribution; only the repo's own `Theorems/` and `Definitions/` content
is included.

Two more per-repo vendoring exclusions from this round, same reasoning as
Anthropic's FLT repo above: `mbrcic/ai-safety-formalization-atlas` vendors
a third-party `TauCeti` library under `vendor/` (136 declarations, unclear
provenance — excluded rather than mislabeled or half-researched), and
`formal-applied-math/formal-mathfin` vendors a `upstream/mathlib/` copy (22
declarations, already covered directly by the real mathlib harvest above).

**Considered and not harvested**:
- CBirkbeck/WeilConverse — an empty Lake template (two files, no actual
  content) rather than the formalization its name suggests.
- jsm28/IMOLean — genuinely statement-only: every `theorem result := by
  sorry` in the repo is an *unsolved* posed IMO problem, by design (it's a
  formalization-conventions repo, not a proof corpus).
- jsm28/bmo2-2020-lean — confirmed Lean 3 (`leanpkg.toml`, no
  `lean-toolchain`).
- Sphere-AI-Lab/FormalMATH-Bench, cmu-l3/minictx-eval — Python evaluation
  harnesses with no `.lean` source of their own (the latter references
  Mathlib/PFR/SciLean/PhysLean as submodules, already covered above); would
  need a different pipeline than `harvest.py`'s clone-and-scan.
- nasqret/DeGiorgi-Explained — confirmed a direct GitHub fork of
  scottnarmstrong/DeGiorgi (byte-identical declaration set, 1,181 names
  overlapping 1,181) — already have it under `degiorgi.jsonl`, harvesting
  the fork too would just double-count the same proofs.
- yangky11/miniF2F-lean4 — confirmed statement-only, same reasoning as
  IMOLean: every theorem is `:= by sorry`, it's a benchmark for provers to
  attempt, not a solved-proof corpus.
- opencompl/lean-gap — genuinely zero `theorem`/`lemma` declarations
  anywhere in the repo; it's an AST + semantics embedding of the GAP
  language (`def`/`inductive` only), nothing proof-shaped to harvest.
- annenkov/two-level, sthamann/tfpt — skipped this round. `two-level` has
  no discoverable `lean-toolchain` anywhere in its tree (ambiguous Lean
  version, possibly a very old pre-Lake setup). `tfpt` does have a real
  `rh/lean` subdirectory with a valid toolchain, but the surrounding repo
  (900+ oddly-named, sequentially-numbered Python scripts spanning
  cosmology, number theory, and cryptography) looks like a large-scale
  speculative research farm rather than a peer-reviewed-adjacent
  formalization effort — flagged for manual review before deciding whether
  its Lean content specifically is worth including.

Every harvested file is filtered for `sorry`: a declaration whose proof contains `sorry` anywhere isn't proven, no matter how confident-looking the rest of it is, and is silently dropped rather than mislabeled as tentative (see `lean_extract.py`'s `_contains_sorry`). This matters most for mixed-status sources like `formal-conjectures`, which stores solved and open problems side by side in the same files, and for Prove2Me, whose own theorem-listing endpoint always returns the posed (`sorry`) form — the real proof is fetched separately, from that theorem's own accepted submission.

## Why `v4.34.0-rc2` is the target toolchain initially

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
failures — a full pull of 50,000+ theorems is on the order of an hour:

```bash
export PROVE2ME_API_KEY=...
python3 tools/harvest_prove2me.py --out data/tentative/prove2me.jsonl
# or bound it for a quicker partial pull: --max 500
```

A full pull is a single large JSONL file (~1.7GB for the current corpus) — too
big for GitHub's 100MB per-file limit. `split_jsonl.py` shards any JSONL file
into git-friendly pieces by cumulative byte size (this is how
`prove2me-001.jsonl` … `prove2me-040.jsonl` were produced):

```bash
python3 tools/split_jsonl.py --in data/tentative/prove2me.jsonl \
  --out-prefix data/tentative/prove2me --max-bytes 41943040
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
