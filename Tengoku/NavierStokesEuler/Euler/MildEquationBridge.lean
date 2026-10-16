import Tengoku.NavierStokesEuler.Euler.DuhamelEquation
import Tengoku.NavierStokesEuler.Euler.SobolevHeatVolterra

/-! The constructed gained-derivative heat fixed point satisfies the actual differential PDE in L². -/

noncomputable section

namespace EulerMildEquationBridge

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerVolterraConvolution EulerDuhamelDifferentiation
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A continuous Sobolev path satisfying the actual ordinary Duhamel formula solves the inhomogeneous L² equation. -/
theorem ordinary_mild_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 ≤ T) (u₀ : SobolevSpace period q)
    (f u : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (hsol : ∀ t : Icc (0 : ℝ) T, u t = heatFlow period q ν t.val u₀ + duhamel period ν T hT f t.val)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT u r))
      (ν • laplacianEvaluation period q hq (u ⟨t, ht.1.le, ht.2.le⟩) +
        value period (f ⟨t, ht.1.le, ht.2.le⟩)) t := by
  have hd := inhomogeneous_heat_value_hasDerivAt period hq ν hν T hT f u₀ t ht
  rw [← hsol ⟨t, ht.1.le, ht.2.le⟩] at hd
  have hf : extendPath T hT f t = f ⟨t, ht.1.le, ht.2.le⟩ := by
    exact congrArg f (projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩)
  rw [hf] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  have he : extendPath T hT u r = u ⟨r, hr.1.le, hr.2.le⟩ :=
    congrArg u (projIcc_of_mem hT ⟨hr.1.le, hr.2.le⟩)
  rw [he, hsol]

end EulerMildEquationBridge
