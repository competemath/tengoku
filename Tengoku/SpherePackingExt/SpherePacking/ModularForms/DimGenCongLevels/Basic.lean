module
public import Tengoku.Seed.NumberTheory.ModularForms.NormTrace
public import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-dimensionality in small weights

This file records basic `FiniteDimensional` results for modular forms on finite-index subgroups of
`SL(2, ℤ)`, using Mathlib's `NormTrace` API.

## Main statements
* `finiteDimensional_modularForm_neg_weight`
* `finiteDimensional_modularForm_weight_zero`
-/

namespace SpherePacking.ModularForms

open scoped MatrixGroups
open UpperHalfPlane ModularForm

noncomputable section

private lemma isArithmetic_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    (Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic :=
  (Subgroup.isArithmetic_iff_finiteIndex (Γ := Γ)).2 inferInstance

end

end SpherePacking.ModularForms
