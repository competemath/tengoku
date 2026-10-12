/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# The degree of a place over the place below it

Let `F' / F` be an algebraic extension of fields, both with the same field of constants `k`, and
let `P'` be a place of `F' / k` lying over the place `P = P'|_F` of `F / k`. The residue fields
then form a tower `k ⊆ F_P ⊆ F'_{P'}`, so the multiplicativity of `Module.finrank` reads

`deg P' = deg P · f(P' ∣ P)`.

This is the same-constant-field case of Stichtenoth, *Algebraic Function Fields and Codes*, 2nd
ed., Corollary 3.1.14, where the general form is cross-multiplied as
`[k' : k] · deg P' = deg P · f(P' ∣ P)`. The extra factor cannot be written here: the residue
field of a place of `F' / k'` is a `k'`-algebra, and the `k`-algebra structure needed to speak of
`Module.finrank k F'_{P'}` at all comes with the constant-field extension theory.

## Main results

* `TauCeti.Place.degree_eq_degree_restrict_mul_relativeDegree`: `deg P' = deg P · f(P' ∣ P)`.
* `TauCeti.Place.degree_restrict_le`: hence `deg P ≤ deg P'`, the form consumed when a
  finiteness statement about places of `F` is transported to `F'`.
* `TauCeti.Place.relativeDegree_eq_one_of_isSepClosed`: a separable extension of a separably closed
  residue field has relative degree `1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1.
-/

public section

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral F F'] (k F) (P' : Place k F')

/-- A separable extension of a separably closed residue field has relative degree `1`. -/
@[simp]
theorem relativeDegree_eq_one_of_isSepClosed [IsSepClosed (P'.restrict k F).ResidueField]
    [Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField] :
    relativeDegree k F P' = 1 := by
  rw [relativeDegree_def, Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact IsSepClosed.algebraMap_bijective _ _

end Place

end TauCeti
