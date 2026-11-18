import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalHom_algebraMap_quotient_of_ne_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalHom_algebraMap_quotient_of_ne_top

open IsLocalRing

theorem solution
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalHom (algebraMap 𝒪 (A ⧸ I)) := by
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.mk_comp_algebraMap]
  exact RingHom.isLocalHom_comp _ _
