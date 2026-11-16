import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AddCommGroup_nonempty_addEquiv_of_forall_natCard_torsionBy_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddCommGroup_nonempty_addEquiv_of_forall_natCard_torsionBy_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

theorem AddCommGroup.nonempty_addEquiv_of_forall_natCard_torsionBy_eq
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (h : ∀ N : ℕ, Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) = Nat.card (Submodule.torsionBy ℤ B (N : ℤ))) :
    Nonempty (A ≃+ B) := by exact @_root_.P2MW.S_AddCommGroup_nonempty_addEquiv_of_forall_natCard_torsionBy_eq.solution A B _ _ _ _ h
