import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower

open scoped TensorProduct

namespace Algebra export _root_.Algebra (commutes TensorProduct.quotIdealMapEquivTensorQuot algebraMap TensorProduct.congr TensorProduct.comm restrictScalars TensorProduct.cancelBaseChange) namespace TensorProduct export _root_.Algebra.TensorProduct (quotIdealMapEquivTensorQuot congr algebraMap_apply map cancelBaseChange) end Algebra.TensorProduct
open scoped _root_.Algebra _root_.Algebra.TensorProduct in
open scoped TensorProduct in

theorem Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower
    (Λ : Type*) [CommRing Λ] (I : Ideal Λ) (k : Type*) [CommRing k] [Algebra Λ k]
    [Algebra (Λ ⧸ I) k] [IsScalarTower Λ (Λ ⧸ I) k]
    (A : Type*) [CommRing A] [Algebra Λ A] :
    Nonempty (k ⊗[Λ] A ≃ₐ[k] k ⊗[Λ ⧸ I] (A ⧸ I.map (algebraMap Λ A))) := by
  let e2 : (Λ ⧸ I) ⊗[Λ] A ≃ₐ[Λ] A ⧸ I.map (algebraMap Λ A) :=
    (Algebra.TensorProduct.comm Λ (Λ ⧸ I) A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.restrictScalars Λ)
  let e2' : (Λ ⧸ I) ⊗[Λ] A ≃ₐ[Λ ⧸ I] A ⧸ I.map (algebraMap Λ A) :=
    AlgEquiv.ofRingEquiv (f := e2.toRingEquiv) (fun x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      exact e2.commutes a)
  exact ⟨(Algebra.TensorProduct.cancelBaseChange Λ (Λ ⧸ I) k k A).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl e2')⟩

theorem solution
    (Λ : Type*) [CommRing Λ] (I : Ideal Λ) (k : Type*) [CommRing k] [Algebra Λ k]
    [Algebra (Λ ⧸ I) k] [IsScalarTower Λ (Λ ⧸ I) k]
    (A : Type*) [CommRing A] [Algebra Λ A] :
    Nonempty (k ⊗[Λ] A ≃ₐ[k] k ⊗[Λ ⧸ I] (A ⧸ I.map (algebraMap Λ A))) :=
  Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower Λ I k A
