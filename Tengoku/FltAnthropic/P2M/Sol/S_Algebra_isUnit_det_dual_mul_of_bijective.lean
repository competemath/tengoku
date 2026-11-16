import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_isUnit_det_dual_mul_of_bijective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_isUnit_det_dual_mul_of_bijective

set_option autoImplicit false

open scoped TensorProduct

namespace Ws23
namespace DLB

open Module

section DLB4

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dualMulMap (τ : Dual R A) : A →ₗ[R] Dual R A := (LinearMap.mul R A).compr₂ τ

theorem coe_dualMulMap (τ : Dual R A) :
    ⇑(dualMulMap R A τ) = fun a : A => τ.comp (LinearMap.mulLeft R a) := by
  funext a
  apply LinearMap.ext
  intro x
  rfl

theorem main4 (b : Basis ι R A) (τ : Dual R A)
    (hτ : Function.Bijective (fun a : A => τ.comp (LinearMap.mulLeft R a))) :
    IsUnit (Matrix.of fun i j => τ (b i * b j)).det := by
  have hbij : Function.Bijective (dualMulMap R A τ) := by rw [coe_dualMulMap]; exact hτ
  let e : A ≃ₗ[R] Dual R A := LinearEquiv.ofBijective (dualMulMap R A τ) hbij
  have hmat : LinearMap.toMatrix b b.dualBasis (e : A →ₗ[R] Dual R A) =
      (Matrix.of fun i j => τ (b i * b j)).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply, Basis.dualBasis_repr, Matrix.transpose_apply, Matrix.of_apply]
    show dualMulMap R A τ (b j) (b i) = τ (b j * b i)
    rfl
  have h := LinearEquiv.isUnit_det e b b.dualBasis
  rwa [hmat, Matrix.det_transpose] at h

end DLB4

end Ws23.DLB

theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (τ : Module.Dual R A)
    (hτ : Function.Bijective (fun a : A => τ.comp (LinearMap.mulLeft R a))) :
    IsUnit (Matrix.of fun i j => τ (b i * b j)).det :=
  Ws23.DLB.main4 R A b τ hτ
