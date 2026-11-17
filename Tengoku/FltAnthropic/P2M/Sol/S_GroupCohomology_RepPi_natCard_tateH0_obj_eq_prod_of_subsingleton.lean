import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_TateCohomology
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepPi
import Tengoku.FltAnthropic.Theorems.Thm_GroupCohomology_RepPi_nonempty_tateH0_obj_linearEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton

set_option autoImplicit false
universe u
open CategoryTheory Rep

/--
@isnad1 id=eq.1h5v.s6.348b767a94aa from=translated src=- shape=c67a02d7 vocab=49645fa4
-/
theorem solution {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (s : Finset ι) (h : ∀ i, i ∉ s → Subsingleton (F i).tateH0) :
    Nat.card (GroupCohomology.RepPi.obj F).tateH0 = ∏ i ∈ s, Nat.card (F i).tateH0 := by
  classical
  obtain ⟨e⟩ := GroupCohomology.RepPi.nonempty_tateH0_obj_linearEquiv F
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun i => (F i).tateH0)),
    Nat.card_prod, Nat.card_pi, Finset.prod_coe_sort s (fun i => Nat.card (F i).tateH0)]
  haveI : ∀ i : {i // ¬ i ∈ s}, Subsingleton (F i).tateH0 := fun i => h i.1 i.2
  rw [Nat.card_of_subsingleton (0 : (i : {i // ¬ i ∈ s}) → (F i).tateH0), mul_one]
