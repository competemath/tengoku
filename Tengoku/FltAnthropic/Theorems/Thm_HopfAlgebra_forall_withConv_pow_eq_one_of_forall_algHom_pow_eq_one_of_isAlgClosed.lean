import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem HopfAlgebra.forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed
    (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Flat R H]
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (hRL : Function.Injective (algebraMap R L))
    (m : ℕ) (hL : ∀ f : WithConv (H →ₐ[R] L), f ^ m = 1)
    (T : Type) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) : f ^ m = 1 := by exact @_root_.P2MW.S_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed.solution R _ _ H _ _ _ _ L _ _ _ _ hRL m hL T _ _ f
