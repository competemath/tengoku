/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.Uniformity
import Tengoku.Seed.Algebra.BigOperators.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directed regular-degree calculus

Phase 10 unit 3 (design freeze in `ARCHITECTURE.md`): the exceptional-degree bound for
a directed relation on a uniform pair, the prerequisite for path and triangle counting.

`degreeDensity R x B = pairDensity R {x} B` is the normalized out-degree of `x` into
`B`. The averaging identity `∑_{x ∈ A} degreeDensity R x B = pairDensity R A B · |A|`
(guard-free) expresses the pair density as an average of one-vertex degrees. The
**strict** exceptional tails
(`lowerDegreeExceptional`/`upperDegreeExceptional`, `ε < |degreeDensity − pairDensity|`
— equality at `ε` is *not* exceptional, matching the `≤ ε` uniformity convention) are
each bounded by `ε·|A|` (`card_lowerDegreeExceptional_le`,
`card_upperDegreeExceptional_le`), so their disjoint union — the absolute-deviation set
(`disjoint_lower_upper`) — is bounded by adding the two separately controlled tails,
giving the safe bound **`2·ε·|A|`** (`card_degreeExceptional_le`). Uniformity controls
each tail only on its own; the two-tail adversarial test exhibits a pair whose two tails
are simultaneously populated with `|union| = |lower| + |upper|`, validating the union
decomposition (it does *not* claim the factor of two is optimal among uniform pairs).

This is an independently authored directed, two-sided generalization; the lower-tail,
positive-density proof architecture is the private `badVertices` /
`card_badVertices_le` argument of `Mathlib.Combinatorics.SimpleGraph.Triangle.Counting`
(Y. Dillies, B. Mehta). `swapRel` and the transpose transport lemmas provide the
incoming-degree surface that path counting needs.
-/

namespace RegularityLemmata

variable {α : Type*} (R : α → α → Prop) [DecidableRel R] {A B T : Finset α} {ε : ℝ}

/-! ### One-vertex degrees and the averaging identity -/

/-- The normalized out-degree of `x` into `B` (guard-free: `0` on empty `B`).-/
noncomputable def degreeDensity (x : α) (B : Finset α) : ℝ := pairDensity R {x} B

theorem degreeDensity_eq (x : α) (B : Finset α) :
    degreeDensity R x B = ((B.filter (R x ·)).card : ℝ) / B.card := by
  rw [degreeDensity, pairDensity_eq_count_div, pairCount_singleton_left, Finset.card_singleton]
  norm_num

theorem degreeDensity_nonneg (x : α) (B : Finset α) : 0 ≤ degreeDensity R x B := by
  rw [degreeDensity_eq]; positivity

theorem degreeDensity_le_one (x : α) (B : Finset α) : degreeDensity R x B ≤ 1 := by
  rw [degreeDensity]; exact pairDensity_le_one

/-- Fiberwise degree sum for `pairCount`.-/
theorem pairCount_eq_sum_degree (A B : Finset α) :
    pairCount R A B = ∑ x ∈ A, (B.filter (R x ·)).card := by
  rw [pairCount, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm

/-- **The averaging identity** (guard-free): the pair density is the average of the
one-vertex degrees.-/
theorem sum_degreeDensity (A B : Finset α) :
    ∑ x ∈ A, degreeDensity R x B = pairDensity R A B * A.card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp [degreeDensity_eq, pairDensity_eq_count_div]
  · have hAcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
    have hBcard : (B.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hB).ne'
    have hcount : (∑ x ∈ A, ((B.filter (R x ·)).card : ℝ)) = (pairCount R A B : ℝ) := by
      rw [pairCount_eq_sum_degree, Nat.cast_sum]
    rw [Finset.sum_congr rfl fun x _ => degreeDensity_eq R x B, ← Finset.sum_div, hcount,
      pairDensity_eq_count_div]
    field_simp

/-- If every out-degree on a nonempty set is below `c`, so is the pair density.-/
theorem pairDensity_lt_of_forall_lt (hT : T.Nonempty) {c : ℝ}
    (h : ∀ x ∈ T, degreeDensity R x B < c) : pairDensity R T B < c := by
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hsum : ∑ x ∈ T, degreeDensity R x B < c * T.card := by
    calc ∑ x ∈ T, degreeDensity R x B < ∑ _x ∈ T, c := Finset.sum_lt_sum_of_nonempty hT h
      _ = c * T.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [sum_degreeDensity] at hsum
  exact lt_of_mul_lt_mul_right hsum hcard.le

/-- If every out-degree on a nonempty set is above `c`, so is the pair density.-/
theorem lt_pairDensity_of_forall_lt (hT : T.Nonempty) {c : ℝ}
    (h : ∀ x ∈ T, c < degreeDensity R x B) : c < pairDensity R T B := by
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hsum : c * T.card < ∑ x ∈ T, degreeDensity R x B := by
    calc c * T.card = ∑ _x ∈ T, c := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ < ∑ x ∈ T, degreeDensity R x B := Finset.sum_lt_sum_of_nonempty hT h
  rw [sum_degreeDensity] at hsum
  exact lt_of_mul_lt_mul_right hsum hcard.le

/-! ### Transpose transport -/

/-- Uniformity transports to the transpose. `swapRel` and its count/density transport now
live in `RegularityLemmata/Finite/PairDensity.lean`, stated for genuinely heterogeneous carriers;
only the
uniformity statement belongs at this layer.-/
theorem isUniformPair_swapRel (hunif : IsUniformPair R A B ε) :
    IsUniformPair (swapRel R) B A ε := by
  intro B' hB' A' hA' hBc hAc
  rw [pairDensity_swapRel, pairDensity_swapRel]
  exact hunif hA' hB' hAc hBc

theorem isUniformPair_swapRel_iff :
    IsUniformPair (swapRel R) B A ε ↔ IsUniformPair R A B ε :=
  ⟨fun h => isUniformPair_swapRel (swapRel R) h, isUniformPair_swapRel R⟩

/-! ### The exceptional degree sets -/

/-- Left vertices whose out-degree strictly *undershoots* the pair density by `> ε`.-/
noncomputable def lowerDegreeExceptional (A B : Finset α) (ε : ℝ) : Finset α :=
  A.filter fun x => degreeDensity R x B < pairDensity R A B - ε

/-- Left vertices whose out-degree strictly *overshoots* the pair density by `> ε`.-/
noncomputable def upperDegreeExceptional (A B : Finset α) (ε : ℝ) : Finset α :=
  A.filter fun x => pairDensity R A B + ε < degreeDensity R x B

/-- The absolute-deviation exceptional set.-/
noncomputable def degreeExceptional [DecidableEq α] (A B : Finset α) (ε : ℝ) : Finset α :=
  lowerDegreeExceptional R A B ε ∪ upperDegreeExceptional R A B ε

theorem mem_lowerDegreeExceptional {x : α} :
    x ∈ lowerDegreeExceptional R A B ε
      ↔ x ∈ A ∧ degreeDensity R x B < pairDensity R A B - ε := by
  rw [lowerDegreeExceptional, Finset.mem_filter]

theorem mem_upperDegreeExceptional {x : α} :
    x ∈ upperDegreeExceptional R A B ε
      ↔ x ∈ A ∧ pairDensity R A B + ε < degreeDensity R x B := by
  rw [upperDegreeExceptional, Finset.mem_filter]

theorem degreeExceptional_subset [DecidableEq α] : degreeExceptional R A B ε ⊆ A := by
  rw [degreeExceptional]
  exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The two tails are disjoint once `0 ≤ ε`: no vertex both under- and overshoots.-/
theorem disjoint_lower_upper (hε : 0 ≤ ε) :
    Disjoint (lowerDegreeExceptional R A B ε) (upperDegreeExceptional R A B ε) := by
  rw [Finset.disjoint_left]
  intro x hxl hxu
  rw [lowerDegreeExceptional, Finset.mem_filter] at hxl
  rw [upperDegreeExceptional, Finset.mem_filter] at hxu
  linarith [hxl.2, hxu.2]

theorem mem_degreeExceptional_iff [DecidableEq α] {x : α} :
    x ∈ degreeExceptional R A B ε
      ↔ x ∈ A ∧ ε < |degreeDensity R x B - pairDensity R A B| := by
  rw [degreeExceptional, Finset.mem_union, mem_lowerDegreeExceptional,
    mem_upperDegreeExceptional, lt_abs]
  constructor
  · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
    · exact ⟨hx, Or.inr (by linarith)⟩
    · exact ⟨hx, Or.inl (by linarith)⟩
  · rintro ⟨hx, h | h⟩
    · exact Or.inr ⟨hx, by linarith⟩
    · exact Or.inl ⟨hx, by linarith⟩

/-- **Good-vertex elimination** (the form path counting consumes): a vertex of `A` that
is not exceptional has degree within `ε` of the pair density.-/
theorem abs_degreeDensity_sub_le_of_not_mem [DecidableEq α] {x : α} (hx : x ∈ A)
    (hxE : x ∉ degreeExceptional R A B ε) :
    |degreeDensity R x B - pairDensity R A B| ≤ ε := by
  rw [mem_degreeExceptional_iff] at hxE
  push Not at hxE
  exact hxE hx

theorem card_degreeExceptional_eq_add [DecidableEq α] (hε : 0 ≤ ε) :
    (degreeExceptional R A B ε).card
      = (lowerDegreeExceptional R A B ε).card + (upperDegreeExceptional R A B ε).card := by
  rw [degreeExceptional, Finset.card_union_of_disjoint (disjoint_lower_upper R hε)]

/-- **Lower-tail bound.**-/
theorem card_lowerDegreeExceptional_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hunif : IsUniformPair R A B ε) :
    ((lowerDegreeExceptional R A B ε).card : ℝ) ≤ ε * A.card := by
  by_contra hcon
  push Not at hcon
  have hTA : lowerDegreeExceptional R A B ε ⊆ A := Finset.filter_subset _ _
  have hTne : (lowerDegreeExceptional R A B ε).Nonempty := by
    rw [← Finset.card_pos]
    have h0 : (0 : ℝ) < (lowerDegreeExceptional R A B ε).card :=
      lt_of_le_of_lt (mul_nonneg hε0 (Nat.cast_nonneg _)) hcon
    exact_mod_cast h0
  have hBB : ε * (B.card : ℝ) ≤ (B.card : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) B.card]
  have hdev := hunif hTA (Finset.Subset.refl B) hcon.le hBB
  have hlt : pairDensity R (lowerDegreeExceptional R A B ε) B < pairDensity R A B - ε :=
    pairDensity_lt_of_forall_lt R hTne fun x hx => (Finset.mem_filter.mp hx).2
  rw [abs_le] at hdev
  linarith [hdev.1]

/-- **Upper-tail bound.**-/
theorem card_upperDegreeExceptional_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hunif : IsUniformPair R A B ε) :
    ((upperDegreeExceptional R A B ε).card : ℝ) ≤ ε * A.card := by
  by_contra hcon
  push Not at hcon
  have hTA : upperDegreeExceptional R A B ε ⊆ A := Finset.filter_subset _ _
  have hTne : (upperDegreeExceptional R A B ε).Nonempty := by
    rw [← Finset.card_pos]
    have h0 : (0 : ℝ) < (upperDegreeExceptional R A B ε).card :=
      lt_of_le_of_lt (mul_nonneg hε0 (Nat.cast_nonneg _)) hcon
    exact_mod_cast h0
  have hBB : ε * (B.card : ℝ) ≤ (B.card : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) B.card]
  have hdev := hunif hTA (Finset.Subset.refl B) hcon.le hBB
  have hgt : pairDensity R A B + ε < pairDensity R (upperDegreeExceptional R A B ε) B :=
    lt_pairDensity_of_forall_lt R hTne fun x hx => (Finset.mem_filter.mp hx).2
  rw [abs_le] at hdev
  linarith [hdev.2]

/-- **The two-sided exceptional bound**: the absolute-deviation set has the *safe*
bound `2·ε·|A|`, because the two one-sided tails are bounded separately (uniformity
cannot be applied to the absolute set directly — see the factor-two test).-/
theorem card_degreeExceptional_le [DecidableEq α] (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hunif : IsUniformPair R A B ε) :
    ((degreeExceptional R A B ε).card : ℝ) ≤ 2 * ε * A.card := by
  have hl := card_lowerDegreeExceptional_le R hε0 hε1 hunif
  have hu := card_upperDegreeExceptional_le R hε0 hε1 hunif
  have hcard : ((degreeExceptional R A B ε).card : ℝ)
      ≤ (lowerDegreeExceptional R A B ε).card + (upperDegreeExceptional R A B ε).card := by
    rw [degreeExceptional]
    exact_mod_cast Finset.card_union_le _ _
  linarith

/-! ### Tests and adversarial examples -/

section Tests

-- Empty target: every out-degree is `0`, and (for `0 ≤ ε`) neither tail can be
-- exceptional, so the guard-free empty side is inert.

end Tests

end RegularityLemmata
