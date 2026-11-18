import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open scoped TensorProduct in

theorem HopfAlgebra.tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt
    (p : ℕ) (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (a b : H ⊗[GaloisRep.ratLocalizedAt p] H)
    (hab : ∀ f g : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
      Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) a =
        Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) b) :
    a = b := by exact @_root_.P2MW.S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt.solution p H _ _ _ _ a b hab
