module

public import Tengoku.SpherePackingExt.SpherePacking.MagicFunction.IntegralParametrisations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuity of integral parametrisations

This file records continuity lemmas for the parametrisations `z₁`--`z₅` and their extensions
`z₁'`--`z₅'`.
-/

namespace MagicFunction.Parametrisations

noncomputable section

open scoped Topology
open Complex Real Set

private lemma continuous_coe_Icc_toComplex :
    Continuous (fun t : Icc (0 : ℝ) 1 => (t : ℂ)) :=
  Complex.continuous_ofReal.comp continuous_subtype_val

end

end MagicFunction.Parametrisations
