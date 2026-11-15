import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits

theorem CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq {C : Type w} [Category.{v} C] {X X' S T : C}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [HasPullback f t] [HasPullback f' t] :
    IsPullback (pullback.fst f' t)
      (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ]) (by rw [Category.comp_id, Category.id_comp]))
      π (pullback.fst f t) := by exact @_root_.P2MW.S_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq.solution C _ X X' S T f f' t π hπ _ _
