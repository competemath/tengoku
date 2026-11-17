import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_TateCohomology
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepPi
import Tengoku.FltAnthropic.Theorems.Thm_GroupCohomology_RepPi_nonempty_tateHneg1_obj_linearEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GroupCohomology_RepPi_subsingleton_tateHneg1_obj.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GroupCohomology_RepPi_subsingleton_tateHneg1_obj

set_option autoImplicit false
universe u
open CategoryTheory Rep

/--
@isnad1 id=subsingl.1h4v.s5.d7ce768199bd from=translated src=- shape=1e366bdd vocab=522814b0
-/
theorem solution {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (h : ∀ i, Subsingleton (F i).tateHneg1) :
    Subsingleton (GroupCohomology.RepPi.obj F).tateHneg1 := by
  obtain ⟨e⟩ := GroupCohomology.RepPi.nonempty_tateHneg1_obj_linearEquiv F
  exact e.toEquiv.subsingleton_congr.2 inferInstance
