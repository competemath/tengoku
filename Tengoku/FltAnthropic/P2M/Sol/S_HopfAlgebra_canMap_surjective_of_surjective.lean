import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_canMap_surjective_of_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_canMap_surjective_of_surjective

set_option autoImplicit false
set_option maxHeartbeats 6400000

open scoped TensorProduct
open HopfAlgebra

namespace P2mS17CS

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [Bialgebra R B]
variable (π : A →ₐc[R] B)

/--
@isnad1 id=eq.0h5v.s10.01ed83dc610b from=translated src=- shape=120aafc4 vocab=73b2fc7e
-/
theorem canAlgHom_tmul_one (a : A) : canAlgHom π (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 := by
  rw [canAlgHom_tmul, map_one, mul_one]

/--
@isnad1 id=eq.0h5v.s12.f7001b99c5ff from=translated src=- shape=d6edd67d vocab=2a6e9a15
-/
theorem canAlgHom_antipode_comul (a' : A) :
    canAlgHom π ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a')) = (1 : A) ⊗ₜ[R] π a' := by

  set Φ : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] B :=
    (π : A →ₐ[R] B).toLinearMap.lTensor A ∘ₗ
      (LinearMap.mul' R A).rTensor A ∘ₗ
      ((HopfAlgebra.antipode R (A := A)).rTensor A).rTensor A with hΦ

  have step1 : (canAlgHom π : A ⊗[R] A →ₐ[R] A ⊗[R] B).toLinearMap
        ∘ₗ (HopfAlgebra.antipode R (A := A)).rTensor A
      = Φ ∘ₗ (TensorProduct.assoc R A A A).symm.toLinearMap
          ∘ₗ (Coalgebra.comul (R := R) (A := A)).lTensor A :=
    TensorProduct.ext' fun u v => by
      have inner : ∀ z : A ⊗[R] A,
          ((HopfAlgebra.antipode R u : A) ⊗ₜ[R] (1 : B)) *
              (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)) z
            = Φ ((TensorProduct.assoc R A A A).symm (u ⊗ₜ[R] z)) := fun z => by
        induction z with
        | zero => simp [hΦ]
        | add x y hx hy =>
            simp only [map_add, mul_add, TensorProduct.tmul_add] at *; rw [hx, hy]
        | tmul x y =>
            simp only [hΦ, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.assoc_symm_tmul,
              LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
              LinearMap.lTensor_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
        canAlgHom_tmul, HopfAlgebra.coaction, AlgHom.comp_apply]
      exact inner _

  have step2 : canAlgHom π ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a'))
      = Φ ((Coalgebra.comul (R := R) (A := A)).rTensor A (Coalgebra.comul a')) := by
    have h := LinearMap.congr_fun step1 (Coalgebra.comul (R := R) a')
    have hco := LinearMap.congr_fun (Coalgebra.coassoc (R := R) (A := A)) a'
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_coe] at h hco
    rw [h, ← hco, LinearEquiv.symm_apply_apply]

  rw [step2, hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
    ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, LinearMap.comp_assoc,
    HopfAlgebra.mul_antipode_rTensor_comul (R := R) (A := A),
    LinearMap.rTensor_comp_apply, Coalgebra.rTensor_counit_comul,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  simp

/--
@isnad1 id=surjecti.1h4v.s11.466884525820 from=translated src=- shape=564ba5cc vocab=347dc2b5
-/
theorem canAlgHom_surjective (hπ : Function.Surjective π) : Function.Surjective (canAlgHom π) := fun z => by
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a c =>
      obtain ⟨a', ha'⟩ := hπ c
      exact ⟨(a ⊗ₜ[R] (1 : A)) *
          ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a')), by
        rw [_root_.map_mul, canAlgHom_tmul_one, canAlgHom_antipode_comul, ha',
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]⟩
  | add y z hy hz =>
      obtain ⟨py, hy⟩ := hy; obtain ⟨pz, hz⟩ := hz
      exact ⟨py + pz, by rw [map_add, hy, hz]⟩

end P2mS17CS

open P2mS17CS in
/--
@isnad1 id=surjecti.1h4v.s11.4920b9c7eeb4 from=translated src=- shape=edcfc0b9 vocab=7448b86f
-/
theorem solution {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    {B : Type*} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Function.Surjective (HopfAlgebra.canMap π) :=
  canAlgHom_surjective π hπ
