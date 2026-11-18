import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearIndependent_linearMap_baseChange_of_int.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearIndependent_linearMap_baseChange_of_int

open scoped TensorProduct

namespace FixlFacesA

/--
@isnad1 id=eq.0h5v.s10.802b7512f607 from=translated src=- shape=408c6d0f vocab=1d30ac9f
-/
theorem matrixEquivTensor_symm_smul (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    (n : Type) [Fintype n] [DecidableEq n] (a : A) (x : A ⊗[R] Matrix n n R) :
    (matrixEquivTensor n R A).symm (a • x) = a • (matrixEquivTensor n R A).symm x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b M =>
    rw [TensorProduct.smul_tmul', matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm,
      smul_eq_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/--
@isnad1 id=linearin.1h5v.s7.cba4f5793796 from=translated src=- shape=ff6d0395 vocab=d7246bca
-/
theorem linearIndependent_matrix_map (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (n : Type) [Fintype n] [DecidableEq n] {ι : Type} (M : ι → Matrix n n R)
    (hM : LinearIndependent R M) :
    LinearIndependent A (fun i => (M i).map (algebraMap R A)) := by
  have h1 : LinearIndependent A (fun i => (1 : A) ⊗ₜ[R] M i) :=
    Module.Flat.linearIndependent_one_tmul hM
  have h2 := h1.map_of_injective_injective id (matrixEquivTensor n R A).symm.toAddEquiv.toAddMonoidHom
    (fun _ h => h) (fun x hx => by simpa using hx)
    (fun a x => by simpa using matrixEquivTensor_symm_smul R A n a x)
  convert h2 using 1
  · funext i
    simp [matrixEquivTensor_apply_symm]
  all_goals first | rfl | exact Subsingleton.elim _ _

end FixlFacesA

open FixlFacesA in

/--
@isnad1 id=linearin.1h4v.s10.ad1d5735923e from=translated src=- shape=b9775113 vocab=b8778101
-/
theorem solution (K : Type) [Field K] [CharZero K]
    (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] {ι : Type}
    (f : ι → Module.End ℤ Λ) (hf : LinearIndependent ℤ f) :
    LinearIndependent K (fun i => ((f i).baseChange K : Module.End K (K ⊗[ℤ] Λ))) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let bK := Algebra.TensorProduct.basis K b
  refine LinearIndependent.of_comp (LinearMap.toMatrix bK bK).toLinearMap ?_
  have key : ((LinearMap.toMatrix bK bK).toLinearMap ∘ fun i => ((f i).baseChange K : Module.End K (K ⊗[ℤ] Λ)))
      = fun i => (LinearMap.toMatrix b b (f i)).map (algebraMap ℤ K) := by
    funext i
    exact LinearMap.toMatrix_baseChange K (f i) b b
  rw [key]
  have hM : LinearIndependent ℤ (fun i => LinearMap.toMatrix b b (f i)) :=
    hf.map' (LinearMap.toMatrix b b).toLinearMap (LinearEquiv.ker _)
  exact linearIndependent_matrix_map ℤ K _ (fun i => LinearMap.toMatrix b b (f i)) hM
