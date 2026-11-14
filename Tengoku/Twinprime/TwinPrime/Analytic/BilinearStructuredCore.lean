import Tengoku.Twinprime.TwinPrime.Analytic.DispersionActiveBudget
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionSquareFactor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Simultaneous removal of large gcds and large prime squares

The square-factor error is controlled in factorwise absolute mass, so it
remains bounded after the small-gcd restriction. No cancellation of the
remaining original signed coefficient is asserted.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

def bilinearStructuredCore (U V X G H : ℕ) : ℝ := by
  classical
  exact ∑ dr ∈ (bilinearPairs U V X).filter
      (fun dr => Nat.gcd dr.1 dr.2 ≤ G ∧ ¬largePrimeSquareInput H (dr.1 * dr.2)),
    (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)

def bilinearSmallGcdLargeSquare (U V X G H : ℕ) : ℝ := by
  classical
  exact ∑ dr ∈ (bilinearPairs U V X).filter
      (fun dr => Nat.gcd dr.1 dr.2 ≤ G ∧ largePrimeSquareInput H (dr.1 * dr.2)),
    (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)

/-- Every squarefree input survives both restrictions; no claim of
cancellation on this remaining range follows from the removals.-/
theorem structuredCore_condition_of_squarefree (d r G H : ℕ)
    (hG : 1 ≤ G) (hs : Squarefree (d * r)) :
    Nat.gcd d r ≤ G ∧ ¬largePrimeSquareInput H (d * r) := by
  refine ⟨?_, ?_⟩
  · simpa only [(Nat.coprime_of_squarefree_mul hs).gcd_eq_one] using hG
  · rintro ⟨p, hp, _, hpp⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp) (by simpa only [pow_two] using hpp)

theorem bilinearSmallGcd_eq_core_add_square (U V X G H : ℕ) :
    bilinearSmallGcd U V X G =
      bilinearStructuredCore U V X G H + bilinearSmallGcdLargeSquare U V X G H := by
  classical
  simp only [bilinearSmallGcd, bilinearStructuredCore, bilinearSmallGcdLargeSquare,
    sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro dr _
  by_cases hg : Nat.gcd dr.1 dr.2 ≤ G <;>
    by_cases hs : largePrimeSquareInput H (dr.1 * dr.2) <;> simp [hg, hs]

theorem abs_bilinearSmallGcdLargeSquare_le_mass (U V X G H : ℕ) :
    |bilinearSmallGcdLargeSquare U V X G H| ≤ bilinearLargePrimeSquareAbsMass U V X H := by
  classical
  unfold bilinearSmallGcdLargeSquare bilinearLargePrimeSquareAbsMass
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro dr hdr
    exact mem_filter.mpr ⟨(mem_filter.mp hdr).1, (mem_filter.mp hdr).2.2⟩
  · intro _ _ _
    exact abs_nonneg _

theorem abs_bilinear_sub_structuredCore_le (U V X G H : ℕ) :
    |bilinearTerm U V X - bilinearStructuredCore U V X G H| ≤
      |bilinearLargeGcd U V X G| + bilinearLargePrimeSquareAbsMass U V X H := by
  rw [bilinearTerm_eq_smallGcd_add_largeGcd U V X G,
    bilinearSmallGcd_eq_core_add_square U V X G H]
  have he : bilinearStructuredCore U V X G H + bilinearSmallGcdLargeSquare U V X G H +
      bilinearLargeGcd U V X G - bilinearStructuredCore U V X G H =
      bilinearLargeGcd U V X G + bilinearSmallGcdLargeSquare U V X G H := by ring
  rw [he]
  exact (abs_add_le _ _).trans
    (_root_.add_le_add le_rfl (abs_bilinearSmallGcdLargeSquare_le_mass U V X G H))

def primaryBilinearStructuredCore (X : ℕ) : ℝ :=
  bilinearStructuredCore (primaryCutoff X) (primaryCutoff X) X
    (dispersionGcdCutoff X) (dispersionGcdCutoff X)

theorem abs_primary_bilinear_sub_structuredCore_div_le (X : ℕ) (hX : 128 ≤ X) :
    |bilinearTerm (primaryCutoff X) (primaryCutoff X) X - primaryBilinearStructuredCore X| / X ≤
      (24 * (2 / Real.log 2) + 8) / (Real.log (4 * (X : ℝ) + 4)) ^ 7 := by
  have h := div_le_div_of_nonneg_right
    (abs_bilinear_sub_structuredCore_le (primaryCutoff X) (primaryCutoff X) X
      (dispersionGcdCutoff X) (dispersionGcdCutoff X))
    (Nat.cast_nonneg X : (0 : ℝ) ≤ _)
  rw [add_div] at h
  calc
    _ ≤ |primaryBilinearLargeGcd X| / X +
        bilinearLargePrimeSquareAbsMass (primaryCutoff X) (primaryCutoff X) X
          (dispersionGcdCutoff X) / X := h
    _ ≤ 24 * (2 / Real.log 2) / (Real.log (4 * (X : ℝ) + 4)) ^ 7 +
        8 / (Real.log (4 * (X : ℝ) + 4)) ^ 7 :=
      _root_.add_le_add (abs_primaryBilinearLargeGcd_div_le_log_seven X hX)
        (bilinearLargePrimeSquareAbsMass_div_le_log _ _ X (by omega))
    _ = _ := by rw [add_div]

theorem tendsto_primary_bilinear_sub_structuredCore_div :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (primaryCutoff X) (primaryCutoff X) X - primaryBilinearStructuredCore X) / X)
      atTop (𝓝 0) := by
  have harg : Tendsto (fun X : ℕ => 4 * (X : ℝ) + 4) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with X
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp harg)
  have hu : Tendsto (fun X : ℕ =>
      (24 * (2 / Real.log 2) + 8) / (Real.log (4 * (X : ℝ) + 4)) ^ 7) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, inv_pow, zero_pow (by decide : 7 ≠ 0),
      mul_zero] using (hinv.pow 7).const_mul (24 * (2 / Real.log 2) + 8)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 128] with X hX
    dsimp only [Function.comp_def]
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)]
    exact abs_primary_bilinear_sub_structuredCore_div_le X hX

end TwinPrime.Analytic
