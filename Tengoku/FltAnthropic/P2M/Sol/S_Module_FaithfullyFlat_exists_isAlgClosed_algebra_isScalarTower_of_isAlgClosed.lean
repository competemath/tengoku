import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=ex.0h3v.s8.c76700482c93 from=translated src=- shape=f1800b8b vocab=1a74a6fa
-/
theorem solution
    (R W k : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
    [Field k] [IsAlgClosed k] [Algebra R k] :
    ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (_ : Algebra R k') (_ : Algebra W k') (_ : Algebra k k'),
      IsScalarTower R W k' ∧ IsScalarTower R k k' := by
  classical
  haveI : Nontrivial (k ⊗[R] W) := inferInstance
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (k ⊗[R] W)
  haveI := h𝔪
  letI : Field ((k ⊗[R] W) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨π⟩ : Nonempty (k ⊗[R] W →+* AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
    ⟨(algebraMap ((k ⊗[R] W) ⧸ 𝔪) (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪))).comp (Ideal.Quotient.mk 𝔪)⟩
  refine ⟨AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪), inferInstance, inferInstance,
    (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra,
    (π.comp (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := W)).toRingHom).toAlgebra,
    (π.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := k) (B := W))).toAlgebra, ?_, ?_⟩
  · letI : Algebra R (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) := (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra
    letI : Algebra W (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
      (π.comp (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := W)).toRingHom).toAlgebra
    exact IsScalarTower.of_algebraMap_eq (fun r => by
      show π (algebraMap R (k ⊗[R] W) r) = π (Algebra.TensorProduct.includeRight (algebraMap R W r))
      rw [AlgHom.commutes])
  · letI : Algebra R (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) := (π.comp (algebraMap R (k ⊗[R] W))).toAlgebra
    letI : Algebra k (AlgebraicClosure ((k ⊗[R] W) ⧸ 𝔪)) :=
      (π.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := k) (B := W))).toAlgebra
    exact IsScalarTower.of_algebraMap_eq (fun r => by
      show π (algebraMap R (k ⊗[R] W) r) = π (Algebra.TensorProduct.includeLeftRingHom (algebraMap R k r))
      rfl)
