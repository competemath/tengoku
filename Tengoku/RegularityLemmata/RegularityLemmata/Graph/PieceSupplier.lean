/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.IndependentSet
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.Uniformity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route (b) supplier checkpoint, item 2: the piece-supplier obligation (statement)

`ARCHITECTURE.md` route (b), supplier checkpoint (2026-07-22). This file carries the
piece-family PREDICATE and the checkpoint's permanent gates.

**The supplier summit is proved** (2026-07-25): `pieceSupplier` and
`exists_pieceFamily` in `RegularityLemmata/Graph/PieceSchedule.lean`, from the extraction of
`RegularityLemmata/Graph/PieceExtraction.lean`. Until then it was recorded in prose only, per the
repository policy that unproved summits are never Lean `Prop` placeholders; the gates
below stay permanent. Its signature demands `0 < t`: gate G-S2 below shows the
zero-target instance is FALSE.

* `IsPieceFamily` — `t` pairwise-disjoint pieces inside a host `A`, of EQUAL
  cardinality `m`, with every ordered pair of distinct pieces `τ`-uniform for every
  relation of a finite family (ordered pairs quantified, so both directions).
* Gate **G-S1**: weighted bad-pair mass does NOT bound the unweighted bad-pair
  count. One heavy cell and seven unit cells with EVERY distinct ordered pair bad:
  the weighted mass passes the `τ = 3/49` regularity-style test, yet every
  pairwise-clean subfamily is a singleton — while an unweighted conversion at this
  `τ` would promise three clean pieces. Equal (or fixed-`Λ`-comparable) sizes must
  come BEFORE the independent-set extraction of `RegularityLemmata/Finite/IndependentSet.lean`, and
  the readily available candidate cells retain only a `1/(2q)` fraction with `q`
  the output fine-part bound — a supplier tolerance `≤ target/(2q)` would recreate
  the circularity route (b) exists to avoid.

Provenance: the supplier is step 1 of the Lemma 3.6 construction in D. Conlon and
J. Fox, *Graph removal lemmas* (arXiv:1211.3487, §3.2) — there obtained from a
cylinder regularity lemma (their Lemma 3.4), or more weakly from Szemerédi plus
Turán; see `PROVENANCE.md` for the precise formalization scope.
-/

namespace RegularityLemmata

/-! ### The piece-family predicate -/

/-- `t` pairwise-disjoint pieces inside `A`, of equal cardinality `m`, with every
ordered pair of DISTINCT pieces `τ`-uniform for every relation of the family.-/
def IsPieceFamily {V : Type*} {K : ℕ} (Rk : Fin K → V → V → Prop)
    [∀ k, DecidableRel (Rk k)] (A : Finset V) (τ : ℝ) {t : ℕ} (m : ℕ)
    (P : Fin t → Finset V) : Prop :=
  (∀ i, P i ⊆ A) ∧
  (∀ i j : Fin t, i ≠ j → Disjoint (P i) (P j)) ∧
  (∀ i, (P i).card = m) ∧
  (∀ k : Fin K, ∀ i j : Fin t, i ≠ j → IsUniformPair (Rk k) (P i) (P j) τ)

/-! ### Gate G-S1 — weighted mass does not bound unweighted counts -/

section Gates

/-- One heavy cell and seven unit cells: the weight profile of the checkpoint
counterexample.-/
private abbrev wS : Fin 8 → ℕ := ![343, 1, 1, 1, 1, 1, 1, 1]

-- The weighted bad-pair mass of the ALL-pairs-bad relation passes the
-- regularity-style test at `τ = 3/49` (in multiplication form:
-- `49·mass ≤ 3·(Σw)²`, i.e. `49·4844 ≤ 3·350²`)…

/-! ### Gate G-S2 — the zero-target rejection -/

-- With `t = 0` a piece family exists VACUOUSLY at any tolerance and any claimed
-- common size…

end Gates

end RegularityLemmata
