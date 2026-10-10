import Tengoku.NavierStokesEuler.Euler.TransverseForwardInverse
import Tengoku.NavierStokesEuler.Euler.LinearDuhamelParameter
import Tengoku.NavierStokesEuler.Euler.ContinuousGramPath

/-!
# Genuine parameter regularity of the transverse forward inverse

The source coefficient is formed from the actual Gram inverse and frame
coefficients. These constructions and the forced forward solve are smooth
in the uniform time norm, without assuming parameter regularity of the
homogeneous evolution supplied by (H3).
-/

noncomputable section

namespace EulerTransverseForwardRegularity

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerContinuousPathComposition EulerContinuousGramPath EulerTransverseGramPath
  EulerTransverseForwardInverse EulerLinearDuhamel
open scoped ContDiff

variable {P V E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T) (Q Q₁ : P → C(Icc (0 : ℝ) T,V →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)

variable (U : ∀ x, Evolution T hT (generator T (Q x) (Q₁ x) c hc (hQ x)))
  (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → V)

end EulerTransverseForwardRegularity
