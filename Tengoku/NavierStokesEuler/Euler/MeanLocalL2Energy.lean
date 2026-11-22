import Tengoku.NavierStokesEuler.Euler.MeanHarmonicSmallBall

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Local energies of actual L² fields, including the decomposition estimate. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal

def localL2Energy (s : Set Space) (u : L2) : ℝ := ∫ x in s, ‖u x‖ ^ 2

/--
@isnad1 id=eq.0h1v.s13.9d068c8fae56 from=translated src=- shape=04d4edd3 vocab=e8b76022
-/
theorem lpNorm_coe_L2 (u : L2) : lpNorm (u : Space → Space) 2 volume = ‖u‖ := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.memLp u).aestronglyMeasurable]

/--
@isnad1 id=integrab.0h1v.s12.12e7d30a7a4c from=translated src=- shape=61315809 vocab=71570476
-/
theorem integrable_norm_sq_L2 (u : L2) : Integrable (fun x => ‖u x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq (Lp.memLp u).norm.aestronglyMeasurable).1 (Lp.memLp u).norm

/--
@isnad1 id=eq.0h1v.s13.3d63589fc610 from=translated src=- shape=da97e0e4 vocab=7e6e3344
-/
theorem integral_norm_sq_L2 (u : L2) : (∫ x, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
  rw [← lpNorm_sq_eq_integral_norm_sq _ (Lp.memLp u), lpNorm_coe_L2]

/--
@isnad1 id=le.0h2v.s11.e4ee54fe5d72 from=translated src=- shape=5623498e vocab=f1dbc40d
-/
theorem localL2Energy_nonneg (s : Set Space) (u : L2) : 0 ≤ localL2Energy s u :=
  integral_nonneg (fun _ => sq_nonneg _)

/--
@isnad1 id=le.0h2v.s12.0b8ae81430a5 from=translated src=- shape=4a637950 vocab=426bf677
-/
theorem localL2Energy_le (s : Set Space) (u : L2) : localL2Energy s u ≤ ‖u‖ ^ 2 := by
  rw [← integral_norm_sq_L2]
  exact setIntegral_le_integral (integrable_norm_sq_L2 u)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/--
@isnad1 id=le.0h2v.s8.94ac468d2bd3 from=translated src=- shape=50b7fd6a vocab=08a295f3
-/
theorem norm_add_sq_le_twice (a b : Space) :
    ‖a+b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a+b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

/--
@isnad1 id=le.0h3v.s14.1a17f5be06f5 from=translated src=- shape=8efc1ed5 vocab=e37cefff
-/
theorem localL2Energy_add_le (s : Set Space) (u v : L2) :
    localL2Energy s (u+v) ≤ 2 * localL2Energy s u + 2 * localL2Energy s v := by
  have hu := (integrable_norm_sq_L2 u).integrableOn (s := s)
  have hv := (integrable_norm_sq_L2 v).integrableOn (s := s)
  calc
    _ ≤ ∫ x in s, 2 * ‖u x‖^2 + 2 * ‖v x‖^2 := by
      apply integral_mono_ae (integrable_norm_sq_L2 (u+v)).integrableOn
        ((hu.const_mul 2).add (hv.const_mul 2))
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_add u v)] with x hx
      rw [hx]
      exact norm_add_sq_le_twice (u x) (v x)
    _ = _ := by
      rw [integral_add (hu.const_mul 2) (hv.const_mul 2), integral_const_mul, integral_const_mul]
      rfl

/--
@isnad1 id=le.0h3v.s14.88aac74187af from=translated src=- shape=fbce4ac1 vocab=8dcbacc9
-/
theorem localL2Energy_le_of_decomposition (s : Set Space) (z w : L2) :
    localL2Energy s z ≤ 2 * localL2Energy s (z-w) + 2 * ‖w‖^2 := by
  have H := localL2Energy_add_le s (z-w) w
  rw [sub_add_cancel] at H
  have hw := localL2Energy_le s w
  linarith

/--
@isnad1 id=le.2h3v.s13.fc484cc911a1 from=translated src=- shape=f194a390 vocab=a459e96f
-/
theorem localL2Energy_ball_le_of_ae_bound (u : L2) (C r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Space) r → ‖u x‖^2 ≤ C) :
    localL2Energy (Metric.ball (0 : Space) r) u ≤ (Real.pi * 4 / 3) * r^3 * C := by
  calc
    _ ≤ ∫ _x in Metric.ball (0 : Space) r, C := by
      apply integral_mono_ae (integrable_norm_sq_L2 u).integrableOn
        (integrableOn_const (measure_ball_lt_top.ne))
      exact (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 hbound
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul]
      change (volume (Metric.ball (0 : Space) r)).toReal * C = _
      rw [volume_ball_toReal r hr]
      ring

end EulerMeanHarmonic
