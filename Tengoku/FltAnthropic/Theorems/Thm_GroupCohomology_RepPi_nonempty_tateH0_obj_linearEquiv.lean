import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_TateCohomology
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepPi
import Tengoku.FltAnthropic.P2M.Sol.S_GroupCohomology_RepPi_nonempty_tateH0_obj_linearEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GroupCohomology_RepPi_nonempty_tateH0_obj_linearEquiv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem GroupCohomology.RepPi.nonempty_tateH0_obj_linearEquiv {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) :
    Nonempty ((GroupCohomology.RepPi.obj F).tateH0 ≃ₗ[k] ((i : ι) → (F i).tateH0)) := by exact @_root_.P2MW.S_GroupCohomology_RepPi_nonempty_tateH0_obj_linearEquiv.solution k G ι _ _ _ F
