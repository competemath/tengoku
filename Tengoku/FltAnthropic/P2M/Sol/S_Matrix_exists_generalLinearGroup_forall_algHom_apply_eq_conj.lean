import Tengoku.Seed.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Tengoku.Seed.RingTheory.SimpleRing.Matrix
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_exists_generalLinearGroup_forall_algHom_apply_eq_conj.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_exists_generalLinearGroup_forall_algHom_apply_eq_conj

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=ex.0h3v.s8.efa82134abc4 from=translated src=- shape=9542f8c0 vocab=5661e516
-/
theorem solution
    (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n K →ₐ[K] Matrix n n K) :
    ∃ u : GL n K, ∀ x : Matrix n n K,
      f x = (u : Matrix n n K) * x * ((u⁻¹ : GL n K) : Matrix n n K) := by
  have hinj : Function.Injective f := RingHom.injective f.toRingHom
  have hsurj : Function.Surjective f := LinearMap.surjective_of_injective (f := f.toLinearMap) hinj
  let F : Matrix n n K ≃ₐ[K] Matrix n n K := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hF : ∀ x, F x = f x := fun _ => rfl
  let G : Module.End K (n → K) ≃ₐ[K] Module.End K (n → K) :=
    (Matrix.toLinAlgEquiv'.symm.trans F).trans Matrix.toLinAlgEquiv'
  obtain ⟨T, hT⟩ := G.eq_linearEquivConjAlgEquiv
  have hG : ∀ x : Matrix n n K, Matrix.toLin' (f x) = T.toLinearMap ∘ₗ Matrix.toLin' x ∘ₗ T.symm.toLinearMap := by
    intro x
    have e0 : ∀ y : Matrix n n K, Matrix.toLin' y = Matrix.toLinAlgEquiv' y := fun _ => rfl
    have h1 : G (Matrix.toLin' x) = Matrix.toLin' (f x) := by
      show Matrix.toLinAlgEquiv' (F (Matrix.toLinAlgEquiv'.symm (Matrix.toLin' x))) = Matrix.toLin' (f x)
      rw [e0, e0, AlgEquiv.symm_apply_apply, hF]
    rw [← h1, hT, LinearEquiv.conjAlgEquiv_apply]
  refine ⟨⟨LinearMap.toMatrix' T.toLinearMap, LinearMap.toMatrix' T.symm.toLinearMap, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · intro x
    have h := congrArg LinearMap.toMatrix' (hG x)
    rw [LinearMap.toMatrix'_toLin'] at h
    rw [h, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.mul_assoc]
    rfl
