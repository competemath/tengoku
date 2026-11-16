import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {C Y : Scheme.{u}} [IsIntegral C] (i : C ⟶ Y) [IsClosedImmersion i] :
    ∃ θ : Y.residueField (i.base (genericPoint C)) ≃+* C.functionField,
      ∀ s : Y.presheaf.stalk (i.base (genericPoint C)),
        θ ((Y.residue (i.base (genericPoint C))).hom s) = (i.stalkMap (genericPoint C)).hom s := by
  set ξ := genericPoint C with hξ
  let φ : Y.presheaf.stalk (i.base ξ) →+* C.functionField := (i.stalkMap ξ).hom
  have hsurj : Function.Surjective φ := i.stalkMap_surjective ξ
  haveI : IsLocalHom φ := i.toLRSHom.prop ξ

  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal _ := by
    ext s
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h hu
      exact not_isUnit_zero (h ▸ hu.map φ)
    · intro h
      by_contra hne
      exact h (isUnit_of_map_unit φ s (isUnit_iff_ne_zero.mpr hne))
  refine ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj), fun s => rfl⟩

