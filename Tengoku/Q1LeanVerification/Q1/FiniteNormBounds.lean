import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Algebra.Order.BigOperators.Ring.Finset
import Tengoku.Seed.Analysis.Normed.Group.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Q1

/-- The finite-support Cauchy--Schwarz bound, with the counting measure and
complex coefficient norm represented by the actual finite sum.
@isnad1 id=le.0h4v.s6.2aea7057f3ba from=translated src=- shape=41f8d728 vocab=053ef67b
-/
theorem sum_norm_le_sqrt_card_mul_sqrt_sum {ι E : Type*} [SeminormedAddCommGroup E]
    (F : Finset ι) (f : ι → E) :
    (∑ i ∈ F, ‖f i‖) ≤ Real.sqrt (F.card : ℝ) *
      Real.sqrt (∑ i ∈ F, ‖f i‖ ^ 2) := by
  have hc : (∑ i ∈ F, ‖f i‖) ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, ‖f i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq F (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  have hs : 0 ≤ ∑ i ∈ F, ‖f i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcard : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg _
  have hsq : (Real.sqrt (F.card : ℝ) * Real.sqrt (∑ i ∈ F, ‖f i‖ ^ 2)) ^ 2 =
      (F.card : ℝ) * ∑ i ∈ F, ‖f i‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcard, Real.sq_sqrt hs]
  have hp : 0 ≤ Real.sqrt (F.card : ℝ) * Real.sqrt (∑ i ∈ F, ‖f i‖ ^ 2) := by positivity
  nlinarith

/-- A squared finite norm bound gives the ratio bound, including a zero
coefficient norm, for which division is zero.
@isnad1 id=le.2h3v.s5.760f7ea9b015 from=translated src=- shape=c4a0b578 vocab=2d4ae70e
-/
theorem ratio_le_sqrt_card_of_norm_bound (a b : ℝ) (m : ℕ)
    (hb : 0 ≤ b)
    (hbound : a ≤ Real.sqrt (m : ℝ) * b) :
    a / b ≤ Real.sqrt (m : ℝ) := by
  by_cases hzero : b = 0
  · simp [hzero]
  · exact (div_le_iff₀ (lt_of_le_of_ne hb (Ne.symm hzero))).mpr hbound

end Q1
