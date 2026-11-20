/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.UnionCenter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route (b) step 1: the equal-cardinality union theorem

`ARCHITECTURE.md` route (b) ladder, step 1 (design freeze 2026-07-20;
reviewer-specified statement 2026-07-21): a union of `s` pairwise-disjoint pieces of
COMMON positive cardinality, with every ordered pair of distinct pieces `α`-uniform
and all those densities within `α` of a common `d ∈ [0, 1]`, satisfies the exact
four-term estimate

    |density(X, Y) − density(U, U)| ≤ 3α + 2α/ε + 1/(s·ε) + 1/s

on `ε`-large test sets, with stable term meanings: `3α` — pair regularity,
density-class width, and comparison of `density(U, U)` with the class center;
`2α/ε` — pieces on which `X` or `Y` is too small to invoke pair regularity;
`1/(s·ε)` — the uncontrolled within-piece contribution inside `X × Y`; `1/s` — the
within-piece contribution to `density(U, U)`. The diagonal bound is the equal-size
estimate (costing `1/(s·ε)`, NOT `1/(s·ε²)`), which is what makes `α = (ε/3)²`,
`s ≥ 2/α` viable (`isUniformPair_self_union`, displayed error at most `2ε/3`).

Equal cardinality is a genuine hypothesis: comparable-but-unequal pieces incur a
comparability factor `Λ` in both within-piece terms (gate G-U2), and the frozen
design trims comparable pieces to equal size FIRST via
`RegularityLemmata/Graph/UniformSlicing.lean`. The `α·m ≤ |X∩Aᵢ|` cutoff is inclusive (gate G-U4),
matching `IsUniformPair`.

**A single common center is a genuine hypothesis too, and it is what breaks the
DIRECTED self-union composition** (gate G-U5, 2026-07-26): `hclose` demands one `d`
for EVERY ordered pair, while the density-bucket extraction
(`RegularityLemmata/Finite/DensityBuckets.lean`) aligns a forward class and a reverse class which by
gate G-U3 need not agree. For the strict order relation they are `1` and `0`, no
center is within `α < 1/2` of both, and indeed no positive-linear-size self-uniform
subset exists at tolerance `1/4`. The theorems in this file are unaffected and
remain valid — what fails is the proposed route (b) step 1 composition for arbitrary
directed relations; see `ARCHITECTURE.md`.

Provenance: this adapts the Lemma 3.6 self-regular-subset construction of
D. Conlon and J. Fox, *Graph removal lemmas* (arXiv:1211.3487, §3.2) to directed
finite binary palettes; the piece supplier follows the weaker
regularity-plus-independent-set route the survey mentions, so no tower-type bound
is claimed, and the full cylinder lemma and their quantitative bounds are NOT
formalized (see `PROVENANCE.md`). The substrate lives in `RegularityLemmata/Graph/UnionCenter.lean`.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V] {R : V → V → Prop} [DecidableRel R]

section Union

variable {s m : ℕ} {A : Fin s → Finset V} {α d ε : ℝ} {U X Y : Finset V}

/-- **The generic union estimate**, with the exact four-term error.
@isnad1 id=le.15h11v.s8.3484d6e39729 from=translated src=- shape=89c3a92d vocab=5861c3a3
-/
theorem pairDensity_union_sub_self_le (hm : 0 < m) (hs : 0 < s)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m)
    (hα : 0 < α) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hunif : ∀ i j : Fin s, i ≠ j → IsUniformPair R (A i) (A j) α)
    (hclose : ∀ i j : Fin s, i ≠ j → |pairDensity R (A i) (A j) - d| ≤ α)
    (hU : U = Finset.univ.biUnion A) (hX : X ⊆ U) (hY : Y ⊆ U)
    (hε : 0 < ε) (hXl : ε * (U.card : ℝ) ≤ (X.card : ℝ))
    (hYl : ε * (U.card : ℝ) ≤ (Y.card : ℝ)) :
    |pairDensity R X Y - pairDensity R U U|
      ≤ 3 * α + 2 * α / ε + 1 / ((s : ℝ) * ε) + 1 / (s : ℝ) := by
  have h1 := pairDensity_union_close_center hm hs hdisj hcard hα hd0 hd1 hunif
    hclose hU hX hY hε hXl hYl
  have h2 := pairDensity_union_self_close_center hm hs hdisj hcard hα hd0 hd1
    hclose hU
  calc |pairDensity R X Y - pairDensity R U U|
      ≤ |pairDensity R X Y - d| + |d - pairDensity R U U| := abs_sub_le _ _ _
    _ ≤ (2 * α + 2 * α / ε + 1 / ((s : ℝ) * ε)) + (α + 1 / (s : ℝ)) := by
        refine add_le_add h1 ?_
        rw [abs_sub_comm]
        exact h2
    _ = 3 * α + 2 * α / ε + 1 / ((s : ℝ) * ε) + 1 / (s : ℝ) := by ring

/-- **The self-uniformity corollary at the frozen constants**: with `α = (ε/3)²` and
`2 ≤ α·s`, the union is `ε`-uniform with itself — the displayed error is at most
`2ε/3`, leaving slack for later slicing and palette bookkeeping.
@isnad1 id=isunifor.12h8v.s8.f9cd098732b9 from=translated src=- shape=9745fe9c vocab=c40ad323
-/
theorem isUniformPair_self_union (hm : 0 < m) (hs : 0 < s)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m)
    (hunif : ∀ i j : Fin s, i ≠ j → IsUniformPair R (A i) (A j) ((ε / 3) ^ 2))
    (hclose : ∀ i j : Fin s, i ≠ j →
      |pairDensity R (A i) (A j) - d| ≤ (ε / 3) ^ 2)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hU : U = Finset.univ.biUnion A)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hsα : 2 ≤ (ε / 3) ^ 2 * (s : ℝ)) :
    IsUniformPair R U U ε := by
  intro X' hX' Y' hY' hXc hYc
  have hα : (0 : ℝ) < (ε / 3) ^ 2 := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have htri := pairDensity_union_sub_self_le hm hs hdisj hcard hα hd0 hd1 hunif
    hclose hU hX' hY' hε hXc hYc
  refine le_trans htri ?_
  have e1 : 2 * (ε / 3) ^ 2 / ε = 2 * ε / 9 := by
    field_simp
    ring
  have e2 : 1 / ((s : ℝ) * ε) ≤ ε / 18 := by
    rw [div_le_iff₀ (mul_pos hsR hε)]
    nlinarith [hsα]
  have e3 : 1 / (s : ℝ) ≤ ε ^ 2 / 18 := by
    rw [div_le_iff₀ hsR]
    nlinarith [hsα]
  have e4 : ε ^ 2 ≤ ε := by nlinarith
  linarith [e1, e2, e3, e4]

end Union

/-! ### Tests and adversarial examples -/

section Tests

-- G-U1a: the two ordered singleton pieces of the equality relation are perfectly
-- uniform at ANY nonnegative tolerance — every subrectangle has density zero.

end Tests

end RegularityLemmata
