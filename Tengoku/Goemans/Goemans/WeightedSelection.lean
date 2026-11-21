/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: GPT-5.6 Sol (formalization).
-/
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Finset.Card
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Weighted selection under a uniform cardinality bound

This file proves the elementary rounding fact for the uniform-matroid
polytope.  If nonnegative fractional coordinates lie in `[0, 1]` and have
total mass at most `r`, some set of at most `r` indices has at least their
fractional weighted value.  A strict mass bound gives strict improvement
provided the residual weighted value is positive.

The proof is finite and elementary.  Among the sets of exactly `r` elements,
choose one of maximum weight.  An exchange argument shows that its
least-weight element dominates every element outside the set.  The available
fractional slack inside the set can therefore pay for all fractional weight
outside it.
-/

namespace Goemans

noncomputable section

namespace WeightedSelection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem exists_top_set (c : ι → ℝ) (r : ℕ)
    (hrpos : 0 < r) (hrcard : r < Fintype.card ι) :
    ∃ S : Finset ι, ∃ i₀ : ι,
      S.card = r ∧
      i₀ ∈ S ∧
      (∀ i ∈ S, c i₀ ≤ c i) ∧
      (∀ j ∉ S, c j ≤ c i₀) := by
  classical
  let candidates : Finset (Finset ι) :=
    Finset.univ.filter fun S : Finset ι => S.card = r
  have hcandidates : candidates.Nonempty := by
    obtain ⟨S, -, hScard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
        (Nat.le_of_lt hrcard)
    exact ⟨S, by simp [candidates, hScard]⟩
  obtain ⟨S, hS, hmax⟩ :=
    Finset.exists_max_image candidates (fun T => T.sum c) hcandidates
  have hScard : S.card = r := by
    simpa [candidates] using hS
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (hScard ▸ hrpos)
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image S c hSnonempty
  refine ⟨S, i₀, hScard, hi₀, hmin, ?_⟩
  intro j hj
  have hjErase : j ∉ S.erase i₀ := fun h => hj (Finset.mem_of_mem_erase h)
  have hswapCard : (insert j (S.erase i₀)).card = r := by
    rw [Finset.card_insert_of_notMem hjErase, Finset.card_erase_of_mem hi₀,
      hScard]
    exact Nat.sub_add_cancel hrpos
  have hswapMem : insert j (S.erase i₀) ∈ candidates := by
    simp [candidates, hswapCard]
  have hswap :=
    hmax (insert j (S.erase i₀)) hswapMem
  have hsumErase :
      (S.erase i₀).sum c + c i₀ = S.sum c := by
    exact Finset.sum_erase_add _ _ hi₀
  rw [Finset.sum_insert hjErase] at hswap
  linarith

private theorem sum_split (S : Finset ι) (g : ι → ℝ) :
    (∑ i, g i) =
      S.sum g + Sᶜ.sum g := by
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i => i ∈ S) (f := g)]
  simp only [Finset.subset_univ, Finset.filter_mem_eq_of_subset, add_right_inj]
  congr 1
  ext i
  simp

private theorem card_cast_sum_one {α : Type*} (S : Finset α) :
    (S.card : ℝ) = S.sum fun _ => (1 : ℝ) := by
  simp

omit [DecidableEq ι] in
/-- Uniform-cardinality weighted rounding.  A fractional point of
`{x | 0 ≤ x ≤ 1, ∑ x ≤ r}` is dominated, for every nonnegative linear
objective, by an indicator of a set of cardinality at most `r`.-/
theorem exists_weighted_selection (c f : ι → ℝ) (r : ℕ)
    (hc : ∀ i, 0 ≤ c i)
    (hf0 : ∀ i, 0 ≤ f i)
    (hf1 : ∀ i, f i ≤ 1)
    (hsum : (∑ i, f i) ≤ (r : ℝ)) :
    ∃ S : Finset ι,
      S.card ≤ r ∧
      (∑ i, c i * f i) ≤ S.sum c := by
  classical
  by_cases hrlarge : Fintype.card ι ≤ r
  · refine ⟨Finset.univ, by simpa, ?_⟩
    exact Finset.sum_le_sum fun i _ =>
      mul_le_of_le_one_right (hc i) (hf1 i)
  by_cases hrzero : r = 0
  · subst r
    have hfsumZero : (∑ i, f i) = 0 :=
      le_antisymm (by simpa using hsum) (Finset.sum_nonneg fun i _ => hf0 i)
    have hfzero : ∀ i, f i = 0 := by
      intro i
      apply le_antisymm
      · have hle : f i ≤ ∑ j, f j :=
          Finset.single_le_sum (fun j _ => hf0 j) (Finset.mem_univ i)
        linarith
      · exact hf0 i
    refine ⟨∅, by simp, ?_⟩
    simp [hfzero]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
  have hrcard : r < Fintype.card ι :=
    Nat.lt_of_not_ge hrlarge
  obtain ⟨S, i₀, hScard, hi₀, hinside, houtside⟩ :=
    exists_top_set c r hrpos hrcard
  let a := c i₀
  have ha : 0 ≤ a := hc i₀
  have hout :
      Sᶜ.sum (fun i => c i * f i) ≤
        a * Sᶜ.sum f := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right
        (houtside i (by simpa using hi)) (hf0 i)
  have hin :
      a * S.sum (fun i => 1 - f i) ≤
        S.sum (fun i => c i * (1 - f i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hinside i hi) (sub_nonneg.mpr (hf1 i))
  have hmass :
      Sᶜ.sum f ≤ S.sum (fun i => 1 - f i) := by
    have hsplit := sum_split S f
    have hones := card_cast_sum_one S
    rw [hScard] at hones
    rw [Finset.sum_sub_distrib]
    linarith
  have houtLeDeficit :
      Sᶜ.sum (fun i => c i * f i) ≤
        S.sum (fun i => c i * (1 - f i)) :=
    hout.trans <| (mul_le_mul_of_nonneg_left hmass ha).trans hin
  refine ⟨S, hScard.le, ?_⟩
  rw [sum_split S (fun i => c i * f i)]
  have hcombine :
      S.sum (fun i => c i * f i) +
          S.sum (fun i => c i * (1 - f i)) =
        S.sum c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith [houtLeDeficit, hcombine]

omit [DecidableEq ι] in
/-- Strict uniform-cardinality rounding.  If the total fractional mass is
strictly below the integer rank and some residual weighted value remains,
the selected integral set has strictly larger weight than the fractional
point.-/
theorem exists_strict_weighted_selection (c f : ι → ℝ) (r : ℕ)
    (hc : ∀ i, 0 ≤ c i)
    (hf0 : ∀ i, 0 ≤ f i)
    (hf1 : ∀ i, f i ≤ 1)
    (hsum : (∑ i, f i) < (r : ℝ))
    (hresidual : 0 < ∑ i, c i * (1 - f i)) :
    ∃ S : Finset ι,
      S.card ≤ r ∧
      (∑ i, c i * f i) < S.sum c := by
  classical
  by_cases hrlarge : Fintype.card ι ≤ r
  · refine ⟨Finset.univ, by simpa, ?_⟩
    have hidentity :
        (∑ i, c i) =
          (∑ i, c i * f i) + ∑ i, c i * (1 - f i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hstrict : (∑ i, c i * f i) < ∑ i, c i := by
      linarith [hidentity, hresidual]
    exact hstrict
  have hfsumNonneg : 0 ≤ ∑ i, f i :=
    Finset.sum_nonneg fun i _ => hf0 i
  have hrRealPos : (0 : ℝ) < r := hfsumNonneg.trans_lt hsum
  have hrpos : 0 < r := by
    by_contra hr
    simp only [Nat.not_lt, Nat.le_zero] at hr
    subst r
    norm_num at hrRealPos
  have hrcard : r < Fintype.card ι :=
    Nat.lt_of_not_ge hrlarge
  obtain ⟨S, i₀, hScard, hi₀, hinside, houtside⟩ :=
    exists_top_set c r hrpos hrcard
  let a := c i₀
  have ha : 0 ≤ a := hc i₀
  have hout :
      Sᶜ.sum (fun i => c i * f i) ≤
        a * Sᶜ.sum f := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right
        (houtside i (by simpa using hi)) (hf0 i)
  have hin :
      a * S.sum (fun i => 1 - f i) ≤
        S.sum (fun i => c i * (1 - f i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hinside i hi) (sub_nonneg.mpr (hf1 i))
  have hmass :
      Sᶜ.sum f < S.sum (fun i => 1 - f i) := by
    have hsplit := sum_split S f
    have hones := card_cast_sum_one S
    rw [hScard] at hones
    rw [Finset.sum_sub_distrib]
    linarith
  have hcombine :
      S.sum (fun i => c i * f i) +
          S.sum (fun i => c i * (1 - f i)) =
        S.sum c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨S, hScard.le, ?_⟩
  rw [sum_split S (fun i => c i * f i)]
  by_cases haZero : a = 0
  · have houtZero : Sᶜ.sum (fun i => c i * f i) = 0 := by
      apply le_antisymm
      · simpa [haZero] using hout
      · exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (hf0 i)
    have houtResidualZero :
        Sᶜ.sum (fun i => c i * (1 - f i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hciUpper : c i ≤ 0 :=
        haZero ▸ houtside i (by simpa using hi)
      have hci : c i = 0 := le_antisymm hciUpper (hc i)
      simp [hci]
    have hresidualSplit :=
      sum_split S (fun i => c i * (1 - f i))
    rw [houtResidualZero, add_zero] at hresidualSplit
    linarith
  · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm haZero)
    have hstrict :
        Sᶜ.sum (fun i => c i * f i) <
          S.sum (fun i => c i * (1 - f i)) :=
      hout.trans_lt <| (mul_lt_mul_of_pos_left hmass haPos).trans_le hin
    linarith

/-- Cost-form corollary of strict weighted selection.  The cost of all
unselected indices is strictly smaller than the fractional residual cost.-/
theorem exists_strict_residual_selection (c f : ι → ℝ) (r : ℕ)
    (hc : ∀ i, 0 ≤ c i)
    (hf0 : ∀ i, 0 ≤ f i)
    (hf1 : ∀ i, f i ≤ 1)
    (hsum : (∑ i, f i) < (r : ℝ))
    (hresidual : 0 < ∑ i, c i * (1 - f i)) :
    ∃ S : Finset ι,
      S.card ≤ r ∧
      Sᶜ.sum c < ∑ i, c i * (1 - f i) := by
  obtain ⟨S, hScard, hstrict⟩ :=
    exists_strict_weighted_selection c f r hc hf0 hf1 hsum hresidual
  refine ⟨S, hScard, ?_⟩
  have htotalSplit := sum_split S c
  have hidentity :
      (∑ i, c i) =
        (∑ i, c i * f i) + ∑ i, c i * (1 - f i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith [htotalSplit, hidentity, hstrict]

end WeightedSelection

end

end Goemans
