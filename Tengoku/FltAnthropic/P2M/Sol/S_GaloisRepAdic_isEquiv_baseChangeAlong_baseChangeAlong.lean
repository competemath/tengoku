import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong

set_option autoImplicit false
open scoped TensorProduct

namespace BCBCAProof

theorem aux
    {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : C ⊗[B] (B ⊗[A] ρ.V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
        (LinearMap.baseChange C (LinearMap.baseChange B (ρ.ρ σ)) x) =
      LinearMap.baseChange C (ρ.ρ σ) (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul b v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

end BCBCAProof

theorem solution
    {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (f : A →+* B) (hf : IsLocalHom f) (g : B →+* C) (hg : IsLocalHom g) (ρ : GaloisRepAdic A) :
    ((ρ.baseChangeAlong f hf).baseChangeAlong g hg).IsEquiv
      (ρ.baseChangeAlong (g.comp f) (RingHom.isLocalHom_comp g f)) := by
  classical
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨{ toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
            map_apply := ?_ }⟩
  intro σ x
  exact BCBCAProof.aux ρ σ x
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
