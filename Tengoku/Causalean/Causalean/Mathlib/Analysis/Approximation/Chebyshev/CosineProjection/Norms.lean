module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Definitions
public import Tengoku

/-!
# Uniform measure and L² bridges

These analytic bridges keep continuous-on-interval assumptions local, and identify
the extended square-integral norm with the real square-root norm. No spectral or
Jackson arguments are used in this module.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- [Uniform design on the unit interval has total mass one](goal).
@isnad1 id=eq.0h0v.s4.51464bd20c5b from=translated src=- shape=7c7ab9f0 vocab=a9af7a23
-/
theorem uniformMeasure_univ : uniformMeasure Set.univ = 1 := by
  simp [uniformMeasure, Real.volume_Icc]

/-- [Uniform design is a probability measure](goal).
@isnad1 id=isprobab.0h0v.s2.3154d29dc244 from=translated src=- shape=54c8eceb vocab=c81a0003
-/
instance uniformMeasure_isProbabilityMeasure : IsProbabilityMeasure uniformMeasure :=
  ⟨uniformMeasure_univ⟩

/-- The [uniform integral of a real function](hyp:g) [equals its interval
integral from zero to one](goal), without additional regularity assumptions.
@isnad1 id=eq.0h1v.s5.5c2c0490b0e4 from=translated src=- shape=98d40058 vocab=0c1a43e5
-/
theorem uniformIntegral_eq_intervalIntegral (g : ℝ → ℝ) :
    (∫ x, g x ∂uniformMeasure) = ∫ x in (0 : ℝ)..1, g x := by
  rw [uniformMeasure, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The [extended square-integral norm of a real function](hyp:g)
[equals Mathlib's L² seminorm under uniform design](goal).
@isnad1 id=eq.0h1v.s5.b31456bd31ea from=translated src=- shape=d7541f99 vocab=2ee03c27
-/
theorem extendedL2Norm_eq_eLpNorm (g : ℝ → ℝ) :
    extendedL2Norm g = eLpNorm g 2 uniformMeasure := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat]
  unfold extendedL2Norm
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (abs_nonneg (g x)) 2]
  simp [Real.enorm_eq_ofReal_abs]

/-- A [function continuous on the closed unit interval](hyp:hg) has
[integrable squared absolute value under uniform design](goal).
@isnad1 id=integrab.1h1v.s6.9b78384d3e12 from=translated src=- shape=bade0ae1 vocab=6fc5b7cc
-/
theorem integrable_sq_of_continuousOn {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    Integrable (fun x => |g x| ^ 2) uniformMeasure := by
  exact (hg.abs.pow 2).integrableOn_Icc

/-- For a [function continuous on the closed unit interval](hyp:hg),
[the extended L² norm is the nonnegative embedding of its real L² norm](goal).

Use `ofReal_integral_eq_lintegral_ofReal` for the nonnegative square, followed
by the real/ENNReal square-root bridge. This statement also ensures finiteness.
@isnad1 id=eq.1h1v.s5.e4072648e68d from=translated src=- shape=64bc495a vocab=85a6009c
-/
theorem extendedL2Norm_eq_ofReal {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    extendedL2Norm g = ENNReal.ofReal (l2Norm g) := by
  unfold extendedL2Norm l2Norm
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_of_continuousOn hg)
    (ae_of_all _ fun x => sq_nonneg |g x|)]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (integral_nonneg fun x => sq_nonneg |g x|) (by norm_num), Real.sqrt_eq_rpow]

/-- A [function continuous on the interval](hyp:hg) whose [absolute value is
bounded there](hyp:hB) by a [nonnegative constant](hyp:hB0) has
[L² norm at most that constant](goal).
@isnad1 id=le.3h2v.s6.5fe2f632f24a from=translated src=- shape=ed954e22 vocab=338b8595
-/
theorem l2Norm_le_of_abs_le {g : ℝ → ℝ} {B : ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B) : l2Norm g ≤ B := by
  unfold l2Norm
  apply (Real.sqrt_le_iff).2
  refine ⟨hB0, ?_⟩
  have hi := integral_mono_ae (integrable_sq_of_continuousOn hg)
    (integrable_const (B ^ 2) : Integrable (fun _ : ℝ => B ^ 2) uniformMeasure)
    ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun x hx =>
      pow_le_pow_left₀ (abs_nonneg (g x)) (hB x hx) 2))
  simpa [uniformMeasure, Real.volume_Icc] using hi

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection
