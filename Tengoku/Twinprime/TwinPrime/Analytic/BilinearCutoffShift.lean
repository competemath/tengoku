import Tengoku.Twinprime.TwinPrime.Analytic.TypeICorrelation
import Tengoku.Twinprime.TwinPrime.Analytic.TotientMainAsymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Changing the right cutoff by an exact Type I difference

On an interval lying above both right cutoffs, the two Vaughan identities
have the same von Mangoldt and low-Möbius logarithmic terms. Their difference
therefore identifies the actual signed bilinear cutoff change with a Type I
difference. The finite error keeps both odd-modulus BV errors and the
even-modulus exceptional budgets.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius Topology

namespace TwinPrime.Analytic

/-- Exact cutoff shift, with no positivity assumption on the left cutoff.-/
theorem bilinearTerm_sub_eq_typeITerm_sub (U V W X : ℕ)
    (hV : V ≤ X) (hW : W ≤ X) :
    bilinearTerm U V X - bilinearTerm U W X =
      typeITerm U V X - typeITerm U W X := by
  unfold bilinearTerm typeITerm
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hnX := (mem_Ioc.mp hn).1
  have hv := vaughanIdentity_apply_of_lt U V n (hV.trans_lt hnX)
  have hw := vaughanIdentity_apply_of_lt U W n (hW.trans_lt hnX)
  have hc :
      (moebiusHigh U * vaughanBeta V) n - (moebiusHigh U * vaughanBeta W) n =
        (vaughanCoefficient U V * ArithmeticFunction.zeta) n -
          (vaughanCoefficient U W * ArithmeticFunction.zeta) n := by
    linarith
  simpa only [mul_sub] using congrArg (fun r : ℝ => vonMangoldt (n + 2) * r) hc

/-- Comparable cutoff logarithms preserve a square-logarithmically weighted
limit. The coefficient function is arbitrary and retains its sign.-/
theorem tendsto_mul_log_sq_of_cutoff_log_comparison (F : ℕ → ℝ)
    (hF : Tendsto (fun t : ℕ => F t * (Real.log ((t : ℝ) + 1)) ^ 2)
      atTop (nhds 0))
    (U W : ℕ → ℕ) (hU : Tendsto U atTop atTop) (C : ℝ) (hC : 0 ≤ C)
    (hlog : ∀ᶠ X in atTop,
      Real.log ((W X : ℝ) + 1) ≤ C * Real.log ((U X : ℝ) + 1)) :
    Tendsto (fun X : ℕ => F (U X) * (Real.log ((W X : ℝ) + 1)) ^ 2)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hupper : Tendsto
      (fun X : ℕ => C ^ 2 * |F (U X) * (Real.log ((U X : ℝ) + 1)) ^ 2|)
      atTop (nhds 0) := by
    simpa using ((hF.comp hU).abs.const_mul (C ^ 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun _ => abs_nonneg _
  filter_upwards [hlog] with X hX
  dsimp only [Function.comp_def]
  have hWlog : 0 ≤ Real.log ((W X : ℝ) + 1) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) (W X)
    linarith)
  have hUlog : 0 ≤ Real.log ((U X : ℝ) + 1) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) (U X)
    linarith)
  have hs : (Real.log ((W X : ℝ) + 1)) ^ 2 ≤
      C ^ 2 * (Real.log ((U X : ℝ) + 1)) ^ 2 := by
    nlinarith [mul_le_mul hX hX hWlog (mul_nonneg hC hUlog)]
  simp only [abs_mul,
    abs_of_nonneg (sq_nonneg (Real.log ((W X : ℝ) + 1))),
    abs_of_nonneg (sq_nonneg (Real.log ((U X : ℝ) + 1)))]
  calc
    _ ≤ |F (U X)| * (C ^ 2 * (Real.log ((U X : ℝ) + 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring

/-- The known Möbius/totient square-log limit controls the complete mixed
Type I main coefficient, including the shared-prime correction.-/
theorem tendsto_totientTypeIMain_of_log_comparison
    (hF : Tendsto (fun t : ℕ =>
      oddMoebiusTotientSum t * (Real.log ((t : ℝ) + 1)) ^ 2) atTop (nhds 0))
    (U W : ℕ → ℕ) (hU : Tendsto U atTop atTop) (C : ℝ) (hC : 0 ≤ C)
    (hlog : ∀ᶠ X in atTop,
      Real.log ((W X : ℝ) + 1) ≤ C * Real.log ((U X : ℝ) + 1)) :
    Tendsto (fun X : ℕ => totientTypeIMain (U X) (W X)) atTop (nhds 0) :=
  tendsto_totientTypeIMain (tendsto_oddMoebiusTotientSum_of_log_sq hF) U W hU
    (tendsto_mul_log_sq_of_cutoff_log_comparison oddMoebiusTotientSum hF U W hU C hC hlog)

end TwinPrime.Analytic
