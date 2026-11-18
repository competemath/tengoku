import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u w
/--
@isnad1 id=ex.2h5v.s8.e1661100cc92 from=translated src=- shape=fa5db8d7 vocab=afb86380
-/
theorem HopfOrder.exists_greatest_of_sup_closed_of_le_noetherian
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (P : Subalgebra R A → Prop) (hsup : ∀ S S', P S → P S' → P (S ⊔ S'))
    (M : Subalgebra R A) [IsNoetherian R M] (hle : ∀ S, P S → S ≤ M) (h0 : ∃ S, P S) :
    ∃ S, P S ∧ ∀ S', P S' → S' ≤ S := by exact @_root_.P2MW.S_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian.solution R _ A _ _ P hsup M _ hle h0
