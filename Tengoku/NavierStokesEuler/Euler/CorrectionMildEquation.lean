import Tengoku.NavierStokesEuler.Euler.CorrectionContinuation
import Tengoku.NavierStokesEuler.Euler.EulerCorrectionEquation

namespace EulerCorrectionContinuation
end EulerCorrectionContinuation
namespace MeasureTheory
end MeasureTheory
namespace Set
end Set
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerCorrectionOperators
end EulerCorrectionOperators
namespace EulerQuadraticSource
end EulerQuadraticSource
namespace EulerMildEquationBridge
end EulerMildEquationBridge
namespace EulerSobolevHeatGenerator
end EulerSobolevHeatGenerator
namespace EulerVolterraConvolution
end EulerVolterraConvolution
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Every actual continued mild correction obeys the literal viscous PDE with its genuine coercive pressure. -/

noncomputable section

namespace EulerCorrectionContinuation
open _root_.EulerCorrectionContinuation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerMildEquationBridge EulerSobolevHeatGenerator EulerVolterraConvolution
open _root_.MeasureTheory _root_.Set _root_.EulerLiftedGradientSpace _root_.EulerCylinderSobolevSpace _root_.EulerCorrectionOperators _root_.EulerMildEquationBridge _root_.EulerSobolevHeatGenerator _root_.EulerVolterraConvolution
open _root_.EulerQuadraticSource hiding Coefficients Coefficients.apply Coefficients.apply_bound Coefficients.apply_sub_bound Coefficients.ballBound Coefficients.ballBound_nonneg Coefficients.ballLipschitz Coefficients.ballLipschitz_nonneg Coefficients.casesOn Coefficients.comp Coefficients.comp_apply Coefficients.continuous Coefficients.ctorIdx Coefficients.forcing Coefficients.linear Coefficients.mk Coefficients.mk.inj Coefficients.mk.injEq Coefficients.mk.noConfusion Coefficients.mk.sizeOf_spec Coefficients.noConfusion Coefficients.noConfusionType Coefficients.projection Coefficients.quadratic Coefficients.rec Coefficients.recOn nestedGroup
open scoped Topology _root_.Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The literal PDE follows at every interior time from any actual correction mild solution. -/
theorem correction_mild_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (e : C(Icc (0 : ℝ) T,SobolevSpace period (q+1)))
    (hsol : ∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT e r))
      (ν • laplacianEvaluation period (q+1) (by omega) (e ⟨t,ht.1.le,ht.2.le⟩) -
        value period (D.rawSource period hq (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e ⟨t,ht.1.le,ht.2.le⟩)) -
        (D.metric.coefficient (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩)).operator
          (value period (D.pressure period hq (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e ⟨t,ht.1.le,ht.2.le⟩)))) t := by
  let F := ((D.coefficients period hq).comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    ((D.coefficients period hq).comp (timeInclusion hTS)).continuous
  have hp := viscous_mild_hasDerivAt period (by omega : 2 ≤ q) ν hν T hT 0 F hF e hsol t ht
  change HasDerivAt _ (ν • laplacianEvaluation period (q+1) _ (e ⟨t,ht.1.le,ht.2.le⟩) +
    value period ((D.coefficients period hq).apply (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e ⟨t,ht.1.le,ht.2.le⟩))) t at hp
  rw [D.source_value period hq] at hp
  convert hp using 1
  abel

end EulerCorrectionContinuation
