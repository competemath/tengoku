import Tengoku.NavierStokesEuler.Euler.LpCylinderTranslation
import Tengoku.NavierStokesEuler.Euler.ContinuousTimeIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Initial time integration commutes with the genuine mixed cylinder action. -/

noncomputable section

namespace EulerCylinderPathIntegral

open Set ContinuousLinearMap EulerLpCylinderTranslation EulerLiftedGradientSpace
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (T : ℝ) (hT : 0 ≤ T)

/--
@isnad1 id=eq.1h5v.s18.46df1b324c70 from=translated src=- shape=31c5e9ef vocab=cd6f5268
-/
theorem integral_translate (p : C(Icc (0 : ℝ) T,CylinderL2 P V)) (a : LiftTangent) :
    integral T hT (pathTranslate P a p) = pathTranslate P a (integral T hT p) := by
  apply ContinuousMap.ext
  intro t
  exact (translate P a).intervalIntegral_comp_comm (extendPath T hT p)

/--
@isnad1 id=contdiff.2h4v.s18.155cd08306e3 from=translated src=- shape=c801fa8b vocab=0e270696
-/
theorem integral_orbit_contDiff (p : C(Icc (0 : ℝ) T,CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (integral T hT p)) := by
  have hh := (integral (E := CylinderL2 P V) T hT).contDiff.comp hp
  convert hh using 1
  funext a
  exact (integral_translate P T hT p a).symm

/--
@isnad1 id=contdiff.4h5v.s17.9b5a21c2b471 from=translated src=- shape=922f63f0 vocab=a93dd42e
-/
theorem orbit_contDiff_of_derivative
    (p q : C(Icc (0 : ℝ) T,CylinderL2 P V))
    (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p) := by
  have he : p = integral T hT q := by
    apply ContinuousMap.ext
    intro t
    have hh := eq_initial_add_integral T hT q (extendPath T hT p) hd t
    simpa only [extendPath,projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),hzero,zero_add] using hh
  rw [he]
  exact integral_orbit_contDiff P T hT q hq

end EulerCylinderPathIntegral
