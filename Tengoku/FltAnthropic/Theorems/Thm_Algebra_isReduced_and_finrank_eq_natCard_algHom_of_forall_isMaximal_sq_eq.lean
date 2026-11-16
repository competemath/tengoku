import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω] (S : Type*) [CommRing S] [Algebra Ω S] [Module.Finite Ω S]
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 𝔪 ^ 2 = 𝔪) :
    IsReduced S ∧ Module.finrank Ω S = Nat.card (S →ₐ[Ω] Ω) := by exact @_root_.P2MW.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_isMaximal_sq_eq.solution Ω _ _ S _ _ _ h
