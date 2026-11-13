import Tengoku.Nlalib.NLAlib.Polynomial.FunctionApproximation.ChebyshevPrimitive
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.FourierBoundedVariation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integration by parts for Chebyshev coefficients

The endpoint-integrable sine primitive gives the ordinary AC integral identity
behind coefficient decay. Helpers for `chebyshev-coeff-bv-decay`.
-/

noncomputable section

open Real Set Polynomial Polynomial.Chebyshev MeasureTheory Filter

namespace NLAlib

/-- AC integration by parts expresses a positive Chebyshev coefficient using its derivative.
Source: focused reroutes, Lemma `lem:ip`; helper for `chebyshev-coeff-bv-decay`.
The derivative representative is specified almost everywhere on the interval.
@isnad1 id=eq.3h3v.s7.5769b3d23e99 from=translated src=- shape=a0c9d537 vocab=1ecb31f4
-/
theorem chebyshevCoeff_eq_integral_derivative {u v : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u (-1) 1)
    (huv : ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv u x = v x)
    {k : ℕ} (hk : 0 < k) :
    chebyshevCoeff u k = 2 / (Real.pi * k) *
      ∫ x in -1..1, v x * sin ((k : ℝ) * arccos x) := by
  have hleft : (∫ x in -1..1, u x * deriv (fun t => sin ((k : ℝ) * arccos t)) x) =
      -(k : ℝ) * (∫ x in -1..1, u x * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹) := by
    calc
      _ = ∫ x in -1..1, u x * (-(k : ℝ) * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        dsimp only
        rw [(hasDerivAt_sin_mul_arccos k hx).deriv]
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring
  have hright : (∫ x in -1..1, deriv u x * sin ((k : ℝ) * arccos x)) =
      ∫ x in -1..1, v x * sin ((k : ℝ) * arccos x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [huv] with x hx hxi
    rw [hx (by simpa using uIoc_subset_uIcc hxi)]
  have hibp := hu.integral_mul_deriv_eq_deriv_mul (absolutelyContinuousOnInterval_sin_mul_arccos k)
  rw [hleft, hright] at hibp
  simp only [arccos_one, mul_zero, sin_zero, arccos_neg_one, sin_nat_mul_pi,
    sub_zero, zero_sub] at hibp
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hj : (∫ x in -1..1, u x * (T ℝ (k : ℤ)).eval x * √(1 - x ^ 2)⁻¹) =
      (∫ x in -1..1, v x * sin ((k : ℝ) * arccos x)) / k := by
    apply (eq_div_iff hkreal).mpr
    linarith [hibp]
  rw [chebyshevCoeff_eq_weighted_integral, ite_eq_right hk.ne', hj]
  ring

/-- Cosine substitution turns the derivative integral into a finite trigonometric identity.
Source: focused reroutes, Lemma `lem:ip`; helper for `chebyshev-coeff-bv-decay`.
@isnad1 id=eq.0h2v.s6.1c6adb89519c from=translated src=- shape=45468511 vocab=9581e36c
-/
theorem integral_mul_sin_arccos_eq (v : ℝ → ℝ) (k : ℕ) :
    (∫ x in -1..1, v x * sin ((k : ℝ) * arccos x)) =
      ∫ θ in 0..Real.pi, v (cos θ) * (sin ((k : ℝ) * θ) * sin θ) := by
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun x => v x * sin ((k : ℝ) * arccos x))
    (f := cos) (f' := fun θ => -sin θ) (a := 0) (b := Real.pi)
    (by fun_prop) (fun θ _ => hasDerivAt_cos θ)
    (fun θ hθ => neg_nonpos.mpr (sin_nonneg_of_nonneg_of_le_pi
      (by simpa only [min_eq_left pi_pos.le] using hθ.1.le)
      (by simpa only [max_eq_right pi_pos.le] using hθ.2.le)))
  have hi : (∫ θ in 0..Real.pi,
      ((fun x => v x * sin ((k : ℝ) * arccos x)) ∘ cos) θ * -sin θ) =
      -(∫ θ in 0..Real.pi, v (cos θ) * (sin ((k : ℝ) * θ) * sin θ)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    have ht : θ ∈ Icc (0 : ℝ) Real.pi := by simpa only [uIcc_of_le pi_pos.le] using hθ
    simp only [Function.comp_apply, arccos_cos ht.1 ht.2]
    ring
  rw [hi, cos_zero, cos_pi, intervalIntegral.integral_symm (a := -1) (b := 1)] at hs
  exact neg_injective hs.symm

end NLAlib
