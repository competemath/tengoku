import Tengoku.NavierStokesEuler.Euler.GainedMildFormula
import Tengoku.NavierStokesEuler.Euler.DuhamelPasting

/-! Pasting actual high-order viscous mild solutions preserves the derivative-gaining Duhamel formula. -/

noncomputable section

namespace EulerGainedMildPasting

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerVolterraConvolution EulerDuhamelDifferentiation EulerTimePathGluing EulerDuhamelPasting EulerGainedMildFormula
open scoped Topology

/-- Applying an actual bounded spatial map commutes with matching-endpoint time pasting. -/
theorem gluePath_map_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a,ha,le_rfl⟩ = v ⟨0,le_rfl,hb⟩) (t : Icc (0 : ℝ) (a+b)) :
    A (gluePath a b ha hb u v hmatch t) =
      gluePath a b ha hb (A.compLeftContinuous ℝ (Icc (0 : ℝ) a) u)
        (A.compLeftContinuous ℝ (Icc (0 : ℝ) b) v) (congrArg A hmatch) t := by
  change A (if t.val ≤ a then extendPath a ha u t.val else extendPath b hb v (t.val-a)) =
    if t.val ≤ a then A (extendPath a ha u t.val) else A (extendPath b hb v (t.val-a))
  split <;> rfl

variable (period : ℝ) [Fact (0 < period)]

end EulerGainedMildPasting
