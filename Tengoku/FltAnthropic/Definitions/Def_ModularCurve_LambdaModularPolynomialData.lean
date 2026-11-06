import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LambdaSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure LambdaModularPolynomialData (q : ℕ) [NeZero q] : Type where

  Ψ : Polynomial (Polynomial ℤ)
  monic : Ψ.Monic
  natDegree_eq : Ψ.natDegree = q + 1

  eval_eq_zero : Ψ.eval₂ ((laurentMap (Int.castRingHom ℚ)).comp evalAtLambdaInt) (lambdaNModC ℚ q) = 0

end ModularCurve

end
