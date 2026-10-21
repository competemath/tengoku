import Tengoku.NavierStokesEuler.Euler.ViscosityDefect
import Tengoku.NavierStokesEuler.Euler.ViscosityCauchy

namespace EulerViscousPathDerivative
end EulerViscousPathDerivative
namespace Set
end Set
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerSobolevHeatGenerator
end EulerSobolevHeatGenerator
namespace EulerViscosityDefect
end EulerViscosityDefect
namespace EulerViscosityCauchy
end EulerViscosityCauchy
namespace EulerVolterraConvolution
end EulerVolterraConvolution

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A pointwise viscous derivative expressed as a continuous path. -/

noncomputable section

namespace EulerViscousPathDerivative
open _root_.EulerViscousPathDerivative

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeatGenerator
  EulerViscosityDefect EulerViscosityCauchy EulerVolterraConvolution
open _root_.Set _root_.EulerLiftedGradientSpace _root_.EulerCylinderSobolevSpace _root_.EulerSobolevHeatGenerator _root_.EulerViscosityDefect _root_.EulerViscosityCauchy _root_.EulerVolterraConvolution

variable (period : ℝ) [Fact (0 < period)]

/-- The actual pointwise viscous derivative equals evaluation of its continuous source path. -/
theorem hasDerivAt_path {s q : ℕ} (hs : 2 ≤ s) (ν T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T,SobolevSpace period s))
    (f : C(Icc (0 : ℝ) T,SobolevSpace period q))
    (r : ℝ) (hr : r ∈ Ioo 0 T)
    (hd : HasDerivAt (fun x => value period (extendPath T hT u x))
      (ν • laplacianEvaluation period s hs (u ⟨r,hr.1.le,hr.2.le⟩) +
        value period (f ⟨r,hr.1.le,hr.2.le⟩)) r) :
    HasDerivAt (extendPath T hT (valuePath period T u))
      (extendPath T hT (viscousDefect period hs ν T u + valuePath period T f) r) r := by
  apply hd.congr_deriv
  change _ = (viscousDefect period hs ν T u + valuePath period T f) (projIcc 0 T hT r)
  rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
  rfl

end EulerViscousPathDerivative
