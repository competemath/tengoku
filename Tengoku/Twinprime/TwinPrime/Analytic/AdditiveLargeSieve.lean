import Tengoku.Twinprime.TwinPrime.Analytic.FiniteLargeSieve
import Tengoku.Twinprime.TwinPrime.Analytic.SeparatedReciprocal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An additive large sieve with a harmonic loss

Centered representatives of separated frequencies remain separated on the
real line. Their reciprocal mass controls every off-diagonal Gram row. The
finite Schur inequality then gives the additive large sieve with constant
`(N-M) + H_card/δ`. All spacing and row estimates are proved here.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.0h2v.s7.090a9c801608 from=translated src=- shape=d44f50c0 vocab=d14a867c
-/
theorem unitAddCircle_dist_eq_abs_sub_round (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) = |x - y - round (x - y)| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]

/--
@isnad1 id=le.0h3v.s7.d0a0a5d10211 from=translated src=- shape=30493cc9 vocab=2ee9abea
-/
theorem unitAddCircle_dist_le_abs_sub_int (x y : ℝ) (m : ℤ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ |x - y - m| := by
  rw [unitAddCircle_dist_eq_abs_sub_round]
  exact round_le (x - y) m

/-- Reciprocal distances from a fixed frequency, with the diagonal removed.
@isnad1 id=le.3h5v.s8.72ddb8211970 from=translated src=- shape=ba77bbaf vocab=15facce0
-/
theorem sum_reciprocal_unitAddCircle_dist_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (θ : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ dist (θ i : UnitAddCircle) (θ j : UnitAddCircle))
    (i : ι) (hi : i ∈ s) :
    (∑ j ∈ s.erase i, 1 / dist (θ i : UnitAddCircle) (θ j : UnitAddCircle)) ≤
      2 * (harmonic s.card : ℝ) / δ := by
  classical
  let r : ι → ℝ := fun j => θ i - θ j - round (θ i - θ j)
  let t : Finset ℝ := (s.erase i).image r
  have hr (j : ι) : |r j| = dist (θ i : UnitAddCircle) (θ j : UnitAddCircle) :=
    (unitAddCircle_dist_eq_abs_sub_round (θ i) (θ j)).symm
  have hrbase : ∀ j ∈ s.erase i, δ ≤ |r j| := by
    intro j hj
    rw [hr]
    exact hsep i hi j (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm
  have hrsep : ∀ j ∈ s.erase i, ∀ k ∈ s.erase i, j ≠ k → δ ≤ |r j - r k| := by
    intro j hj k hk hjk
    calc
      δ ≤ dist (θ k : UnitAddCircle) (θ j : UnitAddCircle) :=
        hsep k (mem_of_mem_erase hk) j (mem_of_mem_erase hj) hjk.symm
      _ ≤ |θ k - θ j - ((round (θ i - θ j) - round (θ i - θ k) : ℤ) : ℝ)| :=
        unitAddCircle_dist_le_abs_sub_int (θ k) (θ j) _
      _ = |r j - r k| := by
        dsimp [r]
        push_cast
        congr 1
        ring
  have hinj : ∀ j ∈ s.erase i, ∀ k ∈ s.erase i, r j = r k → j = k := by
    intro j hj k hk heq
    by_contra hne
    have h := hrsep j hj k hk hne
    rw [heq, sub_self, abs_zero] at h
    linarith
  have htbase : ∀ x ∈ t, δ ≤ |x| := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    exact hrbase j hj
  have htsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
    exact hrsep j hj k hk (fun heq => hxy (congrArg r heq))
  calc
    _ = ∑ j ∈ s.erase i, 1 / |r j| := by simp only [hr]
    _ = ∑ x ∈ t, 1 / |x| := by
      dsimp [t]
      rw [sum_image hinj]
    _ ≤ 2 * (harmonic t.card : ℝ) / δ :=
      sum_reciprocal_abs_le_of_separated t δ hδ htbase htsep
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (harmonic_real_mono (card_image_le.trans (card_erase_le))) (by norm_num)) hδ.le

/-- Each full Gram row has its interval-length diagonal and harmonic off-diagonal bound.
@isnad1 id=le.3h7v.s8.822a493437cc from=translated src=- shape=0398dbe5 vocab=bb7d52a9
-/
theorem additive_kernel_row_le_of_separated {ι : Type*} (s : Finset ι)
    (θ : ι → ℝ) (M N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ dist (θ i : UnitAddCircle) (θ j : UnitAddCircle))
    (i : ι) (hi : i ∈ s) :
    (∑ j ∈ s, ‖∑ n ∈ Ico M N, additivePhase (n * (θ i - θ j))‖) ≤
      ((N - M : ℕ) : ℝ) + (harmonic s.card : ℝ) / δ := by
  classical
  have hoff : (∑ j ∈ s.erase i,
      ‖∑ n ∈ Ico M N, additivePhase (n * (θ i - θ j))‖) ≤
      (harmonic s.card : ℝ) / δ := by
    calc
      _ ≤ ∑ j ∈ s.erase i,
          1 / (2 * dist (θ i : UnitAddCircle) (θ j : UnitAddCircle)) := by
        apply sum_le_sum
        intro j hj
        have hd : 0 < dist (θ i : UnitAddCircle) (θ j : UnitAddCircle) :=
          hδ.trans_le (hsep i hi j (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm)
        have h := norm_sum_Ico_phase_mul_conj_le M N (θ i) (θ j) _ hd le_rfl
        rw [sum_Ico_phase_mul_conj_eq] at h
        exact h.trans (min_le_right _ _)
      _ = (∑ j ∈ s.erase i,
          1 / dist (θ i : UnitAddCircle) (θ j : UnitAddCircle)) / 2 := by
        rw [sum_div]
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ (2 * (harmonic s.card : ℝ) / δ) / 2 :=
        div_le_div_of_nonneg_right
          (sum_reciprocal_unitAddCircle_dist_le s θ δ hδ hsep i hi) (by norm_num)
      _ = _ := by ring
  have hdiag : ‖∑ n ∈ Ico M N, additivePhase (n * (θ i - θ i))‖ = (N - M : ℕ) := by
    simp [additivePhase]
  rw [← sum_erase_add s _ hi, hdiag]
  linarith

/-- A proved additive large sieve, with the harmonic logarithmic loss retained.
@isnad1 id=le.2h7v.s8.137a593824d0 from=translated src=- shape=d2843e91 vocab=3b0421a0
-/
theorem additive_large_sieve_of_separated {ι : Type*} (s : Finset ι)
    (θ : ι → ℝ) (a : ℕ → ℂ) (M N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ dist (θ i : UnitAddCircle) (θ j : UnitAddCircle)) :
    (∑ i ∈ s, ‖∑ n ∈ Ico M N, a n * additivePhase (n * θ i)‖ ^ 2) ≤
      (((N - M : ℕ) : ℝ) + (harmonic s.card : ℝ) / δ) *
        ∑ n ∈ Ico M N, ‖a n‖ ^ 2 := by
  apply finite_additive_large_sieve_of_kernel_rows s θ a M N _
  · have hh : (0 : ℝ) ≤ harmonic s.card := by
      simpa using harmonic_real_mono (Nat.zero_le s.card)
    positivity
  · exact additive_kernel_row_le_of_separated s θ M N δ hδ hsep

/-- An elementary logarithmic version of the same finite estimate.
@isnad1 id=le.2h7v.s8.0e62dac15dbb from=translated src=- shape=9ba9ec7f vocab=9c89f865
-/
theorem additive_large_sieve_of_separated_log {ι : Type*} (s : Finset ι)
    (θ : ι → ℝ) (a : ℕ → ℂ) (M N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      δ ≤ dist (θ i : UnitAddCircle) (θ j : UnitAddCircle)) :
    (∑ i ∈ s, ‖∑ n ∈ Ico M N, a n * additivePhase (n * θ i)‖ ^ 2) ≤
      (((N - M : ℕ) : ℝ) + (1 + Real.log s.card) / δ) *
        ∑ n ∈ Ico M N, ‖a n‖ ^ 2 := by
  apply (additive_large_sieve_of_separated s θ a M N δ hδ hsep).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact add_le_add le_rfl (div_le_div_of_nonneg_right (harmonic_le_one_add_log s.card) hδ.le)

end TwinPrime.Analytic
