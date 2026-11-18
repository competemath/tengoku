import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_quotient_of_ne_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_quotient_of_ne_top

open IsLocalRing

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalRing (A ⧸ I) :=
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
