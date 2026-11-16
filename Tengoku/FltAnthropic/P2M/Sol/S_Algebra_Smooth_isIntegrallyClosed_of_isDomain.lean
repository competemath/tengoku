import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_Smooth_isIntegrallyClosed_of_isDomain.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_Smooth_isIntegrallyClosed_of_isDomain

universe u

theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Smooth R S] : IsIntegrallyClosed S := by

  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  haveI := hp.isPrime
  exact (Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime R S p (Localization.AtPrime p)).2
