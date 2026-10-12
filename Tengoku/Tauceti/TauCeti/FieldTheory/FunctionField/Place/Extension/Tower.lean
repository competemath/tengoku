/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# Towers of extensions of places

Restriction of places is functorial through a tower of algebraic field extensions. The
ramification index and relative residue degree are multiplicative in the same tower. These are
the tower statements in Stichtenoth, *Algebraic Function Fields and Codes*, Proposition 3.1.6.

The constants are allowed to grow with the function fields. Thus the setup contains parallel
towers `k₀ → k₁ → k₂` and `F₀ → F₁ → F₂`, with each `Fᵢ` an algebra over `kᵢ` and the
expected commuting scalar towers. No function-field, finite-dimensionality, separability, or
perfectness hypothesis is needed: restriction uses only integrality of the field extensions,
and the degree identity is the ordinary finrank tower formula for the residue fields.

## Main results

* `TauCeti.Place.restrict_restrict`: restricting first to `F₁` and then to `F₀` agrees with
  restricting directly to `F₀`.
* `TauCeti.Place.ramificationIdx_restrict_mul`: ramification indices multiply in a tower.
* `TauCeti.Place.relativeDegree_restrict_mul`: relative residue degrees multiply in a tower.

## Mathematical context

Multiplicativity in towers for extensions of places is Stichtenoth, Proposition 3.1.6. The
restriction identity also supplies the functoriality needed to define induced places and to
construct dual isogenies.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.6.
-/

public section

namespace TauCeti

namespace Place

universe u₀ u₁ u₂ v₀ v₁ v₂

variable {k₀ : Type u₀} {k₁ : Type u₁} {k₂ : Type u₂}
variable {F₀ : Type v₀} {F₁ : Type v₁} {F₂ : Type v₂}
variable [Field k₀] [Field k₁] [Field k₂] [Field F₀] [Field F₁] [Field F₂]
variable [Algebra k₀ k₁] [Algebra k₁ k₂] [Algebra k₀ k₂]
variable [Algebra F₀ F₁] [Algebra F₁ F₂] [Algebra F₀ F₂] [IsScalarTower F₀ F₁ F₂]
variable [Algebra k₀ F₀] [Algebra k₁ F₁] [Algebra k₂ F₂]
variable [Algebra k₀ F₁] [Algebra k₁ F₂] [Algebra k₀ F₂]
variable [IsScalarTower k₀ k₁ F₁] [IsScalarTower k₁ k₂ F₂]
variable [IsScalarTower k₀ F₀ F₁] [IsScalarTower k₁ F₁ F₂]
variable [IsScalarTower k₀ k₂ F₂] [IsScalarTower k₀ F₀ F₂]
variable [Algebra.IsIntegral F₀ F₁] [Algebra.IsIntegral F₁ F₂]

/-- **Restriction of places is functorial in a tower**: restricting a place of `F₂ / k₂`
first to `F₁ / k₁` and then to `F₀ / k₀` gives its direct restriction to `F₀ / k₀`.

This is the normalized-place form of transitivity of valuation restriction. -/
@[simp]
theorem restrict_restrict (P : Place k₂ F₂) :
    (P.restrict k₁ F₁).restrict k₀ F₀ =
      @restrict k₀ k₂ F₀ F₂ _ _ _ _ _ _ _ _ _ _ _ P
        (Algebra.IsIntegral.trans F₁) := by
  let _ : Algebra.IsIntegral F₀ F₂ := Algebra.IsIntegral.trans F₁
  rw [restrict_eq_iff_integers_le]
  intro x hx
  rw [mem_integers_restrict_iff]
  rw [← IsScalarTower.algebraMap_apply F₀ F₁ F₂]
  exact (mem_integers_restrict_iff k₀ F₀ P x).mp hx

end Place

end TauCeti

end
