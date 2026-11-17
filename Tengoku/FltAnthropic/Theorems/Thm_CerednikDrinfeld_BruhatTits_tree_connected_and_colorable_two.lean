import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CerednikDrinfeld.BruhatTits LT.LatticeTree

/--
@isnad1 id=and.0h2v.s6.ded60d552629 from=translated src=- shape=be1858a4 vocab=fb075cab
-/
theorem CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    (tree R K).Connected ∧ (tree R K).Colorable 2 := by exact @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two.solution R _ _ _ K _ _ _
