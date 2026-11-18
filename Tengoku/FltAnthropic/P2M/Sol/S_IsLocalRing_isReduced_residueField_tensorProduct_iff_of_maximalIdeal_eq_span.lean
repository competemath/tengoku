import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span

set_option autoImplicit false

open IsLocalRing TensorProduct

/--
@isnad1 id=iff.1h3v.s9.00cba1ee8494 from=translated src=- shape=95629b09 vocab=5dc989e8
-/
theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] (a : A) (ha : maximalIdeal A = Ideal.span {a})
    (R : Type*) [CommRing R] [Algebra A R] :
    IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ Ideal.span {algebraMap A R a}) := by
  have hI : (maximalIdeal A).map (algebraMap A R) = Ideal.span {algebraMap A R a} := by
    rw [ha, Ideal.map_span, Set.image_singleton]
  let e : ResidueField A ⊗[A] R ≃+* R ⧸ Ideal.span {algebraMap A R a} :=
    ((Algebra.TensorProduct.comm A (ResidueField A) R).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (maximalIdeal A)).symm.restrictScalars A)).toRingEquiv.trans (Ideal.quotEquivOfEq hI)
  exact ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
    fun _ => isReduced_of_injective e e.injective⟩
