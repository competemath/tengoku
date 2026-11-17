import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_irreducible_natCast_ratLocalizedAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_irreducible_natCast_ratLocalizedAt

set_option autoImplicit false

theorem solution (q : ℕ) (hq : q.Prime) :
    Irreducible ((q : ℕ) : GaloisRep.ratLocalizedAt q) := by
  haveI : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q hq
  haveI hprime : (Ideal.span {(q : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hq
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) hq
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]

  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(q : ℤ)}) (GaloisRep.ratLocalizedAt q),
    Ideal.map_span, Set.image_singleton]
  all_goals first | rfl | simp
