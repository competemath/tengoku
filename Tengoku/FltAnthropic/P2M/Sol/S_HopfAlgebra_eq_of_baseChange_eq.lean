import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_eq_of_baseChange_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_eq_of_baseChange_eq

universe u v

set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra
namespace EqOfBaseChange
open _root_.HopfAlgebra

theorem tmul_one_injective
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Function.Injective (fun y : M => (1 : K) ⊗ₜ[R] y) := by
  have h1 : Function.Injective ((Algebra.linearMap R K).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R K)
  intro a b hab
  have key : ((Algebra.linearMap R K).rTensor M) ((TensorProduct.lid R M).symm a) =
      ((Algebra.linearMap R K).rTensor M) ((TensorProduct.lid R M).symm b) := by
    simpa [LinearMap.rTensor_tmul] using hab
  exact (TensorProduct.lid R M).symm.injective (h1 key)

end HopfAlgebra.EqOfBaseChange

open HopfAlgebra.EqOfBaseChange in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ ψ : H →ₐc[R] H')
    (h : (φ : H →ₐ[R] H').toLinearMap.baseChange K = (ψ : H →ₐ[R] H').toLinearMap.baseChange K) :
    φ = ψ := by
  refine DFunLike.ext _ _ fun x => ?_
  have hx := LinearMap.congr_fun h ((1 : K) ⊗ₜ[R] x)
  simp only [LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply] at hx
  exact tmul_one_injective K H' hx
