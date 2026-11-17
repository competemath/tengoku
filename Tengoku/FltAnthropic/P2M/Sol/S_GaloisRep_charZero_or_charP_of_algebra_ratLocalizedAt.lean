import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRep_ratLocalizedAt_isUnit_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt

open GaloisRep

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

/--
@isnad1 id=or.0h2v.s6.87879d29f237 from=translated src=- shape=4804f460 vocab=68d010ae
-/
theorem solution (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*) [Field K]
    [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] :
    CharZero K ∨ CharP K ℓ := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | h0
  · rcases eq_or_ne p ℓ with rfl | hpℓ
    · exact Or.inr hp
    · exfalso
      have hunit : IsUnit ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt ℓ)) := by
        rw [GaloisRep.ratLocalizedAt.isUnit_iff hℓ]
        have hcoe : (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt ℓ)) : ℚ) = (p : ℚ) := by
          push_cast
          ring
        rw [hcoe, Rat.num_natCast, Int.natAbs_natCast]
        exact fun hdvd => hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hprime).mp hdvd).symm
      have hK : IsUnit ((p : ℕ) : K) := by
        have h := hunit.map (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K)
        rwa [map_natCast] at h
      exact hK.ne_zero (CharP.cast_eq_zero K p)
  · subst h0
    exact Or.inl (CharP.charP_to_charZero K)
