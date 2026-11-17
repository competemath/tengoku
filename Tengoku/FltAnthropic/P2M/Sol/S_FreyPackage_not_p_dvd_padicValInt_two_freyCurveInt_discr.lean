import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.Theorems.Thm_FreyPackage_padicValInt_two_freyCurveInt_discr

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr

/--
@isnad1 id=not.0h1v.s4.0c25a529dd4b from=translated src=- shape=d7a104e9 vocab=de297de0
-/
theorem solution (P : FreyPackage) : ¬ P.p ∣ padicValInt 2 P.freyCurveInt.Δ := by
  intro h
  have h8 : P.p ∣ 8 := by
    have h2 : P.p ∣ padicValInt 2 P.freyCurveInt.Δ + 8 :=
      ⟨2 * padicValInt 2 (P.a * P.b * P.c), by rw [P.padicValInt_two_freyCurveInt_discr]; ring⟩
    exact (Nat.dvd_add_right h).mp h2
  have h2 : P.p ∣ 2 := P.pp.dvd_of_dvd_pow (show P.p ∣ 2 ^ 3 by norm_num; exact h8)
  have := (Nat.prime_dvd_prime_iff_eq P.pp Nat.prime_two).mp h2
  have := P.hp5
  omega
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
