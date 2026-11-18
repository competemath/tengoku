import Tengoku.Seed.GroupTheory.Transfer
import Tengoku.Seed.GroupTheory.Abelianization.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MonoidHom_map_transfer_eq_transfer_comp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MonoidHom_map_transfer_eq_transfer_comp

set_option autoImplicit false

/--
@isnad1 id=eq.0h7v.s8.75c40cffdd02 from=translated src=- shape=01e0a5cb vocab=22650b04
-/
theorem solution
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) (g : G) :
    f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g := by
  classical
  rw [MonoidHom.transfer_def ϕ (default : H.LeftTransversal) g,
    MonoidHom.transfer_def (f.comp ϕ) (default : H.LeftTransversal) g]
  unfold Subgroup.leftTransversals.diff
  simp only [map_prod, MonoidHom.comp_apply]
