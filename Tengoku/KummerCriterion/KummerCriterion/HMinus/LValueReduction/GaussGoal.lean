module

public import Tengoku.KummerCriterion.KummerCriterion.HMinus.LValueReduction.Factors
public import Tengoku.KummerCriterion.KummerCriterion.ZetaFactorisation.Basic
import Tengoku.KummerCriterion.KummerCriterion.HMinus.LValueReduction.LValues

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The cyclotomic Gauss-product target

This file isolates the exact Gauss-product identity needed by the final
`hMinus` assembly theorem and rewrites it into the raw odd-character product
shape proved later.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace KummerCriterion

section GaussGoal

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

end GaussGoal

end KummerCriterion
