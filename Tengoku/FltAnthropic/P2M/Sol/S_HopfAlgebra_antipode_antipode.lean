import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_antipode_antipode.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_antipode_antipode

open _root_.Coalgebra open _root_.HopfAlgebra
open scoped _root_.TensorProduct _root_.Coalgebra.TensorProduct

namespace HopfAlgebra
export _root_.HopfAlgebra (antipode_one antipode_mul sum_antipode_mul_eq_algebraMap_counit)
open _root_.HopfAlgebra

section GeneralHopf
variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [HopfAlgebra R A]

private theorem antipode_algebraMap' (r : R) :
    antipode R (algebraMap R A r) = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, antipode_one]

private theorem toConv_antipode_mul_toConv_id' :
    WithConv.toConv (antipode R (A := A)) * WithConv.toConv (LinearMap.id : A →ₗ[R] A)
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_coe, id_eq]
  exact sum_antipode_mul_eq_algebraMap_counit (ℛ R a)

end GeneralHopf

section CommutativeHopf
variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]

private theorem sum_antipode_antipode_mul_antipode' {a : A} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R a ι𝓡) :
    ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
      = algebraMap R A (counit (R := R) a) := by
  calc ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
      = ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i) * 𝓡.right i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [antipode_mul_antidistrib (antipode R (𝓡.left i)) (𝓡.right i)]
        exact mul_comm _ _
    _ = antipode R (∑ i ∈ 𝓡.index, antipode R (𝓡.left i) * 𝓡.right i) := by
        rw [map_sum]
    _ = antipode R (algebraMap R A (counit (R := R) a)) := by
        rw [sum_antipode_mul_eq_algebraMap_counit 𝓡]
    _ = algebraMap R A (counit (R := R) a) := antipode_algebraMap' _

private theorem toConv_antipode_comp_antipode_mul_toConv_antipode' :
    WithConv.toConv (antipode R ∘ₗ antipode R : A →ₗ[R] A)
        * WithConv.toConv (antipode R (A := A))
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
  exact sum_antipode_antipode_mul_antipode' (ℛ R a)

private theorem antipode_comp_antipode' :
    (antipode R ∘ₗ antipode R : A →ₗ[R] A) = LinearMap.id :=
  WithConv.toConv_injective
    (left_inv_eq_right_inv toConv_antipode_comp_antipode_mul_toConv_antipode'
      toConv_antipode_mul_toConv_id')

end CommutativeHopf
end HopfAlgebra

theorem solution {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] [HopfAlgebra R A] (a : A) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (HopfAlgebra.antipode_comp_antipode' (R := R) (A := A)) a
