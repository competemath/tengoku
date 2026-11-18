import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Module.End.eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {D : Type*} [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x)
    (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V)
    {N : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) N) (hN : IsNilpotent N) : N = 0 := by exact @_root_.P2MW.S_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq.solution F _ V _ _ _ D _ _ hD ι hdim N hcomm hN
