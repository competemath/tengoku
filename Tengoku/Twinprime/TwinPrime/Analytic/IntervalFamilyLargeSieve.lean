import Tengoku.Twinprime.TwinPrime.Analytic.DyadicIntervalCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fixed disjoint interval families in a large sieve

Unlike adaptively chosen intervals, a fixed disjoint family can be summed
directly in the fixed-interval estimate. Its coefficient energy is counted
at most once, with no loss for the number of intervals or the tree depth.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

theorem sum_weighted_fixed_disjoint_intervals_sq_le {ι κ : Type*}
    (s : Finset ι) (J : Finset κ) (u v : κ → ℕ) (w : ι → ℝ)
    (f : ι → ℕ → ℂ) (e : ℕ → ℝ) (A : ℝ)
    (he : ∀ n, 0 ≤ e n) (hA : 0 ≤ A)
    (hLS : ∀ a b : ℕ, (∑ i ∈ s, w i * ‖∑ n ∈ Ico a b, f i n‖ ^ 2) ≤
      (((b - a : ℕ) : ℝ) + A) * ∑ n ∈ Ico a b, e n)
    (M R : ℕ)
    (hvalid : ∀ j ∈ J, M ≤ u j ∧ u j ≤ v j ∧ v j ≤ R)
    (hdis : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' →
      Disjoint (Ico (u j) (v j)) (Ico (u j') (v j'))) :
    (∑ i ∈ s, w i * ∑ j ∈ J, ‖∑ n ∈ Ico (u j) (v j), f i n‖ ^ 2) ≤
      (((R - M : ℕ) : ℝ) + A) * ∑ n ∈ Ico M R, e n := by
  have hd : Set.PairwiseDisjoint (↑J) (fun j => Ico (u j) (v j)) := by
    intro j hj j' hj' hne
    exact hdis j hj j' hj' hne
  have hsub : J.biUnion (fun j => Ico (u j) (v j)) ⊆ Ico M R := by
    intro n hn
    obtain ⟨j, hj, hnj⟩ := mem_biUnion.mp hn
    obtain ⟨hu, _, hv⟩ := hvalid j hj
    exact mem_Ico.mpr ⟨hu.trans (mem_Ico.mp hnj).1, (mem_Ico.mp hnj).2.trans_le hv⟩
  have hE : (∑ j ∈ J, ∑ n ∈ Ico (u j) (v j), e n) ≤ ∑ n ∈ Ico M R, e n := by
    rw [← sum_biUnion hd]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => he n)
  calc
    _ = ∑ j ∈ J, ∑ i ∈ s, w i * ‖∑ n ∈ Ico (u j) (v j), f i n‖ ^ 2 := by
      simp only [mul_sum]
      rw [sum_comm]
    _ ≤ ∑ j ∈ J, ((((v j - u j : ℕ) : ℝ) + A) *
        ∑ n ∈ Ico (u j) (v j), e n) := sum_le_sum fun j _ => hLS (u j) (v j)
    _ ≤ ∑ j ∈ J, ((((R - M : ℕ) : ℝ) + A) *
        ∑ n ∈ Ico (u j) (v j), e n) := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun n _ => he n)
      have hb : v j - u j ≤ R - M := by
        obtain ⟨hu, _, hv⟩ := hvalid j hj
        omega
      exact add_le_add (by exact_mod_cast hb) le_rfl
    _ = (((R - M : ℕ) : ℝ) + A) * ∑ j ∈ J, ∑ n ∈ Ico (u j) (v j), e n := by
      rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)

end TwinPrime.Analytic
