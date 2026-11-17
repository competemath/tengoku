import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

/--
@isnad1 id=smooth.1h3v.s9.51ef37b943d4 from=translated src=- shape=a44b9e13 vocab=b11d57c6
-/
theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [JacobsonSpace ↑X]
    (h : ∀ x : ↑X, IsClosed ({x} : Set ↑X) → (f.stalkMap x).hom.FormallySmooth) :
    Smooth f := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  by_contra hne
  have hne' : ((f.smoothLocus : Set ↑X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro htop
    exact hne (TopologicalSpace.Opens.ext htop)
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne' (f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed)
  exact hx ((Scheme.Hom.mem_smoothLocus).mpr (h x hxc))
