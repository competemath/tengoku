import Tengoku.Seed.GroupTheory.Commutator.Basic
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.GroupTheory.SpecificGroups.Cyclic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped commutatorElement

namespace Ihara

universe u

def HasTrivialSchurMultiplier (G : Type u) [Group G] : Prop :=
  ∀ (E : Type u) [Group E] (π : E →* G), Function.Surjective π →
    MonoidHom.ker π ≤ Subgroup.center E → MonoidHom.ker π ≤ commutator E →
      MonoidHom.ker π = ⊥

/--
@isnad1 id=hastrivi.1h3v.s5.141997749d73 from=translated src=- shape=a724b963 vocab=1ac19976
-/
theorem HasTrivialSchurMultiplier.of_mulEquiv {G H : Type u} [Group G] [Group H]
    (hH : HasTrivialSchurMultiplier H) (e : G ≃* H) : HasTrivialSchurMultiplier G := by
  intro E _ π hsurj hcent hcomm
  have hker : MonoidHom.ker (e.toMonoidHom.comp π) = MonoidHom.ker π := by
    ext z
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hsurj' : Function.Surjective (e.toMonoidHom.comp π) := by
    rw [MonoidHom.coe_comp]; exact e.surjective.comp hsurj
  have h := hH E (e.toMonoidHom.comp π) hsurj'
    (by rw [hker]; exact hcent) (by rw [hker]; exact hcomm)
  rw [← hker]; exact h

end Ihara
