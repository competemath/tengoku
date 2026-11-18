import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt

set_option autoImplicit false
open scoped TensorProduct in

/--
@isnad1 id=eq.1h4v.s13.fbe13840b80c from=translated src=- shape=aac5a88a vocab=19aa3407
-/
theorem solution
    (p : ℕ) (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (a b : H ⊗[GaloisRep.ratLocalizedAt p] H)
    (hab : ∀ f g : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
      Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) a =
        Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) b) :
    a = b := by
  apply HopfAlgebra.eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt p
    (H ⊗[GaloisRep.ratLocalizedAt p] H) a b
  intro F
  have hF : F = Algebra.TensorProduct.lift (F.comp Algebra.TensorProduct.includeLeft)
      ((F.restrictScalars (GaloisRep.ratLocalizedAt p)).comp Algebra.TensorProduct.includeRight)
      (fun _ _ => .all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hF]
  exact hab _ _
