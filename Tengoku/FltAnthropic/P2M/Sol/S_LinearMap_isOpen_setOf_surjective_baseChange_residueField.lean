import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearMap_isOpen_setOf_surjective_baseChange_residueField.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearMap_isOpen_setOf_surjective_baseChange_residueField

universe u v w

open TensorProduct

theorem solution
    {A : Type u} [CommRing A] {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (d : P →ₗ[A] Q) [Module.Finite A (Q ⧸ LinearMap.range d)] :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} :=
  by

  have key : ∀ (K : Type u) [CommRing K] [Algebra A K],
      Function.Surjective (d.baseChange K) ↔ Subsingleton (K ⊗[A] (Q ⧸ LinearMap.range d)) := by
    intro K _ _
    rw [(TensorProduct.tensorQuotientEquiv K (LinearMap.range d)).toEquiv.subsingleton_congr,
      Submodule.Quotient.subsingleton_iff, LinearMap.baseChange_eq_ltensor, ← LinearMap.range_eq_top]
    have : (TensorProduct.map LinearMap.id (LinearMap.range d).subtype).range = (LinearMap.lTensor K d).range :=
      (LinearMap.lTensor_range K).symm
    rw [this]

  have h : {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} =
      (Module.support A (Q ⧸ LinearMap.range d))ᶜ := by
    ext 𝔭
    rw [Set.mem_ofPred_eq, key, Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
  rw [h]
  exact Module.isClosed_support.isOpen_compl
