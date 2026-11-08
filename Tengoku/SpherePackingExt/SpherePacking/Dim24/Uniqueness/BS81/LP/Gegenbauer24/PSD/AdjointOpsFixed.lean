module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Adjoint
import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fischer adjointness for basic operators

This file proves the adjointness of multiplication by variables and partial derivatives on
homogeneous pieces, and packages the corresponding adjointness between the degree-`k+2`
Laplacian and multiplication by `r² = ∑ i, X i ^ 2` (implemented via degree-shifting maps).

## Main statements
* `inner_mulXPk_eq_inner_pderivPk`
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset Finsupp MvPolynomial

local notation "Pk" => Pk

open Harmonic

private def e (i : Var) : Var →₀ ℕ := Finsupp.single i 1

lemma add_tsub_e_cancel (i : Var) (d : Var →₀ ℕ) : (d + e i) - e i = d :=
  add_tsub_cancel_right d (e i)

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
