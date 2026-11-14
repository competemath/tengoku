import Tengoku.Twinprime.TwinPrime.Analytic.MertensReduction
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusLogWeight
import Tengoku.Twinprime.TwinPrime.Analytic.WeightedMertens
import Tengoku.Twinprime.TwinPrime.Analytic.ContractionParameters

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A quantitative Selberg-to-Mertens contraction

The centered Selberg summatory estimate gives a genuine contraction of the
weighted Mertens supremum. The small power cutoff is chosen after the absolute
coefficient-mass constant is fixed. No Mertens cancellation estimate is assumed.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

/-- The finite hyperbola head and discrete Abel unweighting give the actual
coefficient that contracts the weighted Mertens supremum.
@isnad1 id=ex.4h3v.s8.8b404d256817 from=translated src=- shape=78cee7a4 vocab=a7e2012a
-/
theorem eventually_weightedMertens_le_sup_coefficient
    (c K δ : ℝ) (hK : 0 ≤ K) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hA : ∀ᶠ t : ℝ in atTop,
      |centeredSelbergSummatory c t| ≤ K * t / (Real.log t) ^ 5) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ x : ℝ in atTop,
      weightedMertens x ≤
        (selbergReciprocalMassConstant c * (δ + 2 / Real.log x) ^ 2 / (1 - δ) ^ 6 +
          (128 * (1 + (14 : ℝ) ^ 5) + 4) / Real.log x) * mertensSup x + E := by
  obtain ⟨E, hE, hsum⟩ :=
    eventually_moebiusLogSqSummatory_le_power_head c K δ hK hδ0 hδ1 hA
  refine ⟨E + (Real.log 2) ^ 2, by positivity, ?_⟩
  have hz := (tendsto_rpow_atTop (by linarith : 0 < 1 - δ)).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hsum, eventually_mertensReal_log_six_le_logSq_sum,
    eventually_log_pow_le_self 4, hz, eventually_ge_atTop (2 : ℝ)]
    with x hsum hunweight hpow hz hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hW : 0 ≤ mertensSup x := mertensSup_nonneg x hx
  have hunweight := hunweight (mertensSup x) hW
    (fun t ht htx => weightedMertens_le_sup ht htx)
  have hhead := normalized_selberg_power_head_le c x δ hx hδ0 hδ1 hz
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum (show 0 ≤ (Real.log x) ^ 4 by positivity)) hx0.le
  have herror : (E * x / (Real.log x) ^ 4) * (Real.log x) ^ 4 / x = E := by
    field_simp
  have hconstant : (Real.log 2) ^ 2 * (Real.log x) ^ 4 / x ≤ (Real.log 2) ^ 2 := by
    apply (div_le_iff₀ hx0).mpr
    exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hsumscale : |moebiusLogSqSummatory x| * (Real.log x) ^ 4 / x ≤
      mertensSup x * (selbergReciprocalMassConstant c * (δ + 2 / Real.log x) ^ 2 /
        (1 - δ) ^ 6) + E := by
    have hsplit : ((∑ k ∈ Ioc 0 ⌊x ^ δ⌋₊,
        |centeredSelbergCoefficient c k| * |mertensReal (x / k)|) +
        E * x / (Real.log x) ^ 4) * (Real.log x) ^ 4 / x =
        (∑ k ∈ Ioc 0 ⌊x ^ δ⌋₊,
          |centeredSelbergCoefficient c k| * |mertensReal (x / k)|) *
          (Real.log x) ^ 4 / x + E := by
      rw [add_mul, add_div, herror]
    rw [hsplit] at hscaled
    exact hscaled.trans (add_le_add hhead le_rfl)
  change weightedMertens x ≤ _ at hunweight
  calc
    _ ≤ (|moebiusLogSqSummatory x| + (Real.log 2) ^ 2) * (Real.log x) ^ 4 / x +
        (128 * (1 + (14 : ℝ) ^ 5) + 4) * mertensSup x / Real.log x := hunweight
    _ ≤ (mertensSup x * (selbergReciprocalMassConstant c * (δ + 2 / Real.log x) ^ 2 /
        (1 - δ) ^ 6) + E) + (Real.log 2) ^ 2 +
        (128 * (1 + (14 : ℝ) ^ 5) + 4) * mertensSup x / Real.log x := by
      rw [add_mul, add_div]
      exact add_le_add (add_le_add hsumscale hconstant) le_rfl
    _ = _ := by ring

/-- A centered Selberg summatory error with five logarithmic powers of
saving implies the ordinary Mertens estimate with six powers.
@isnad1 id=mertensl.2h2v.s6.c5ce1958f16a from=translated src=- shape=3eecd699 vocab=29e515a8
-/
theorem mertensLogSix_of_centeredSelberg_bound (c K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ᶠ t : ℝ in atTop,
      |centeredSelbergSummatory c t| ≤ K * t / (Real.log t) ^ 5) :
    MertensLogSix := by
  obtain ⟨δ, hδ0, hδ1, hcoef⟩ := exists_small_parameter_eventual_contraction
    (selbergReciprocalMassConstant c) (128 * (1 + (14 : ℝ) ^ 5) + 4)
  obtain ⟨E, _hE, hmain⟩ :=
    eventually_weightedMertens_le_sup_coefficient c K δ hK hδ0 hδ1 hA
  have hcontract : ∀ᶠ x : ℝ in atTop,
      weightedMertens x ≤ (1 / 2) * initialIntervalSup weightedMertens 2 x + E := by
    filter_upwards [hcoef, hmain, eventually_ge_atTop (2 : ℝ)] with x hcoef hmain hx
    exact hmain.trans (add_le_add
      (mul_le_mul_of_nonneg_right hcoef (mertensSup_nonneg x hx)) le_rfl)
  obtain ⟨C, hC, hbound⟩ :=
    exists_abs_bound_of_eventually_initialIntervalSup_contraction weightedMertens 2 (1 / 2) E
      weightedMertens_bddAbove
      (fun x hx => weightedMertens_nonneg x (by linarith))
      (by norm_num) (by norm_num) hcontract
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hweight := (hbound N hNr).1
  rw [abs_of_nonneg (weightedMertens_nonneg N hN0.le)] at hweight
  simp only [weightedMertens, mertensReal_eq, Nat.floor_natCast] at hweight
  exact (le_div_iff₀ (pow_pos hlog 6)).mpr ((div_le_iff₀ hN0).mp hweight)

end TwinPrime.Analytic
