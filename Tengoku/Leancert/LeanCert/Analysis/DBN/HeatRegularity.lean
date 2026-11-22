import Tengoku.Leancert.LeanCert.Analysis.DBN.HeatMoments
import Tengoku.Leancert.LeanCert.Analysis.DBN.HeatSymmetry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Joint continuity, entire spatial dependence, and the backward heat equation
for the actual de Bruijn–Newman heat integral. -/
namespace LeanCert.Analysis.DBN
open MeasureTheory Set Filter

/--
@isnad1 id=continuo.0h0v.s5.a0bd191ce507 from=translated src=- shape=dfc9f019 vocab=f585bf75
-/
theorem continuous_H : Continuous (fun p : ℝ × ℂ => H p.1 p.2) := by
  simpa only [moment_zero] using continuous_moment 0

/--
@isnad1 id=hasderiv.0h2v.s5.c8cd6fca35ca from=translated src=- shape=2febc963 vocab=22a2c994
-/
theorem hasDerivAt_H_z (t : ℝ) (z : ℂ) : HasDerivAt (H t) (moment 1 t z) z := by
  have h := hasDerivAt_moment_z 0 t z
  rw [show moment 0 t = H t from funext (moment_zero t)] at h
  exact h

/-- Entire means complex differentiability at every complex argument.
@isnad1 id=differen.0h1v.s6.64961f96f5f0 from=translated src=- shape=e86db131 vocab=03f73f57
-/
theorem H_entire (t : ℝ) : Differentiable ℂ (H t) :=
  fun z => (hasDerivAt_H_z t z).differentiableAt

/--
@isnad1 id=eq.0h1v.s5.70923dd4d060 from=translated src=- shape=ce5a5dfd vocab=283def32
-/
theorem deriv_H_z (t : ℝ) : deriv (H t) = moment 1 t :=
  funext fun z => (hasDerivAt_H_z t z).deriv

/--
@isnad1 id=eq.0h2v.s6.0c62783725d2 from=translated src=- shape=62943192 vocab=283def32
-/
theorem deriv2_H_z (t : ℝ) (z : ℂ) : deriv (deriv (H t)) z = moment 2 t z := by
  rw [deriv_H_z]
  exact (hasDerivAt_moment_z 1 t z).deriv

/--
@isnad1 id=eq.0h3v.s5.781f19fcdf1e from=translated src=- shape=a0a2ab91 vocab=da222bc8
-/
theorem momentIntegrand_two (t : ℝ) (z : ℂ) (u : ℝ) :
    momentIntegrand 2 t z u = -((u : ℂ)^2 * heatIntegrand t z u) := by
  unfold momentIntegrand heatIntegrand
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℂ)*(Real.pi : ℂ)/2 = (Real.pi : ℂ) by ring, Complex.cos_add_pi]
  ring

/--
@isnad1 id=hasderiv.0h3v.s6.34d41e88307a from=translated src=- shape=80c16146 vocab=010072bb
-/
theorem hasDerivAt_heatIntegrand_t (t u : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => heatIntegrand s z u) (-momentIntegrand 2 t z u) t := by
  have hd := (((Real.hasDerivAt_exp (t*u^2)).comp t ((hasDerivAt_id t).mul_const (u^2))).mul_const
    (Phi u)).ofReal_comp.mul_const (Complex.cos (z*(u : ℂ)))
  convert! hd using 1
  rw [momentIntegrand_two]
  unfold heatIntegrand
  push_cast
  ring

/-- Differentiation in real time, including at t=0, with no boundary restriction.
@isnad1 id=hasderiv.0h2v.s6.8c3bdf0c0ad7 from=translated src=- shape=ae5510a3 vocab=69eedaaa
-/
theorem hasDerivAt_H_t (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => H s z) (-moment 2 t z) t := by
  have h := (ParametricIntegral.hasDerivAt_integral
    (fun s u => heatIntegrand s z u) (fun s u => -momentIntegrand 2 s z u)
    (fun s => heatMajorant s z) (fun u : ℝ => u^2*Real.exp (-u^2))
    (by unfold heatMajorant; fun_prop) (integrableOn_gaussian_moment 2)
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u _ => mul_nonneg (sq_nonneg u) (Real.exp_pos _).le))
    (fun s => (measurable_heatIntegrand s z).aestronglyMeasurable)
    (fun s => (measurable_momentIntegrand 2 s z).neg.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu s => by
      simpa only [norm_neg] using momentIntegrand_bound 2 s z hu.le))
    (Eventually.of_forall fun u s => hasDerivAt_heatIntegrand_t s u z)
    t (heatIntegrand_integrable t z)).2
  simpa only [H, moment, integral_neg] using h

/-- Sign dictated by exp(t*u²) and the second derivative of cos(z*u).
@isnad1 id=eq.0h2v.s7.c2a610b45471 from=translated src=- shape=8118602c vocab=ff88d777
-/
theorem heat_equation (t : ℝ) (z : ℂ) :
    deriv (fun s : ℝ => H s z) t = -deriv (deriv (H t)) z := by
  rw [(hasDerivAt_H_t t z).deriv, deriv2_H_z]

end LeanCert.Analysis.DBN
