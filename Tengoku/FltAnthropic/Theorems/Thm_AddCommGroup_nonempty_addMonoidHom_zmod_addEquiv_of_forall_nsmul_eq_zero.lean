import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=nonempty.1h2v.s7.b664340cdf01 from=translated src=- shape=6b5b3124 vocab=a0f05c9e
-/
theorem AddCommGroup.nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
    (L : Type u) [AddCommGroup L] [Finite L] (d : ℕ) [NeZero d] (hd : ∀ x : L, d • x = 0) :
    Nonempty ((L →+ ZMod d) ≃+ L) := by exact @_root_.P2MW.S_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero.solution L _ _ d _ hd
