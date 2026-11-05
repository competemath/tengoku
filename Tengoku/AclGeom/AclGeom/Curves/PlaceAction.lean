/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Divisors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Places transported along automorphisms

A `k`-automorphism `σ` of `F` moves each place of `F/k`: the new valuation ring is the preimage
`σ⁻¹(O)` (`Place.comap`). Pullback of valuation rings reverses composition, so this is an action
of the opposite group of `k`-automorphisms on the places.

For a finitely generated `k`-subalgebra `A` of a one-variable function field over an algebraically
closed field, only finitely many places fail to contain `A` (`Place.boundary_finite`). An
automorphism preserving `A` permutes these places (`Place.comap_mem_boundary_iff`).

Named consumers: the action of a scheme action on the places of a curve's function field and the
boundary of an affine curve (`Correspondence.SchemePlaceAction`), toward blueprint
`lem:affine-action`. This is the field-place analogue of extending automorphisms to a completion;
it does not prove the source's scheme extension statement.

**Status:** proved; the actual scheme and affine-curve consumers are checked independently.
-/

namespace AclGeom

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- The place moved by a `k`-automorphism: its valuation ring is the preimage.-/
def comap (σ : F ≃ₐ[k] F) (P : Place k F) : Place k F where
  val := P.val.comap (σ : F →+* F)
  algebraMap_mem' c := by
    change σ (algebraMap k F c) ∈ P.val
    rw [σ.commutes]
    exact P.algebraMap_mem c
  ne_top' h := P.ne_top <| top_unique fun x _ ↦ by
    have hx : σ.symm x ∈ P.val.comap (σ : F →+* F) := by
      rw [h]
      exact ValuationSubring.mem_top _
    change σ (σ.symm x) ∈ P.val at hx
    rwa [AlgEquiv.apply_symm_apply] at hx

/--
@isnad1 id=iff.0h5v.s7.0cb1e8b07559 from=translated src=- shape=1d41cee7 vocab=37a9253b
-/
theorem mem_comap {σ : F ≃ₐ[k] F} {P : Place k F} {x : F} :
    x ∈ (P.comap σ).val ↔ σ x ∈ P.val :=
  Iff.rfl

/-- Places are determined by their valuation rings.
@isnad1 id=eq.1h4v.s6.243e83ab0da7 from=translated src=- shape=9973d0b2 vocab=34c16585
-/
theorem ext_val {P Q : Place k F} (h : P.val = Q.val) : P = Q := by
  obtain ⟨v, _, _⟩ := P
  obtain ⟨w, _, _⟩ := Q
  dsimp only at h
  subst h
  rfl

/-- The opposite group of `k`-automorphisms acts on places by pulling back valuation rings.-/
instance : MulAction (F ≃ₐ[k] F)ᵐᵒᵖ (Place k F) where
  smul σ P := P.comap σ.unop
  one_smul _ := ext_val (SetLike.ext fun _ ↦ Iff.rfl)
  mul_smul _ _ _ := ext_val (SetLike.ext fun _ ↦ Iff.rfl)

/-- The boundary of a `k`-subalgebra `A`: the places whose valuation ring does not contain `A`.-/
def boundary (A : Subalgebra k F) : Set (Place k F) :=
  {P | ¬ (A : Set F) ⊆ P.val}

end Place

end AclGeom
