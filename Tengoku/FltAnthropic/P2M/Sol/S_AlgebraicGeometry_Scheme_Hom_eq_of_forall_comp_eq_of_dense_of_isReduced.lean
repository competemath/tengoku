import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace DenseSetAgree

/--
@isnad1 id=epi.0h3v.s5.a5d5ffb3314f from=translated src=- shape=033dcc81 vocab=2ee1f001
-/
theorem epi_specMap_of_field {κ k : Type u} [Field κ] [Field k] (φ : CommRingCat.of κ ⟶ CommRingCat.of k) :
    Epi (Spec.map φ) := by
  haveI : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI : Algebra κ k := φ.hom.toAlgebra
    show Module.Flat κ k
    infer_instance
  haveI : Surjective (Spec.map φ) := ⟨fun p => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end DenseSetAgree

/--
@isnad1 id=eq.3h7v.s9.e6e7ed5aaa43 from=translated src=- shape=7d907b65 vocab=c2d37037
-/
theorem solution
    {X Y S : Scheme.{u}} [IsReduced X]
    (F G : X ⟶ Y) (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (D : Set ↥X) (hD : Dense D)
    (h : ∀ x ∈ D, ∃ (k : Type u) (_ : Field k) (y : Spec (CommRingCat.of k) ⟶ X),
      x ∈ Set.range y.base ∧ y ≫ F = y ≫ G) :
    F = G := by
  refine AlgebraicGeometry.ext_of_fromSpecResidueField_eq F G i D hD (fun x hx => ?_) hFG
  obtain ⟨k, _, y, ⟨p, rfl⟩, hy⟩ := h x hx
  obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  haveI := DenseSetAgree.epi_specMap_of_field (X.descResidueField (Scheme.stalkClosedPointTo y))
  rw [← cancel_epi (Spec.map (X.descResidueField (Scheme.stalkClosedPointTo y))), ← Category.assoc, ← Category.assoc,
    X.descResidueField_stalkClosedPointTo_fromSpecResidueField k y]
  exact hy
